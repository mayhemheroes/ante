use crate::cache::{ ModuleCache, DefinitionInfoId, DefinitionKind, DefinitionInfo };
use crate::types::{ self, Type, PrimitiveType, TypeInfoId, TypeInfoBody, TypeConstructor };
use crate::error::location::Location;
use crate::parser::ast;
use crate::refine::Refineable;
use crate::refine::refinements::Refinements;
use crate::util::fmap;

use std::collections::HashMap;

use z3::ast::{ Ast, Bool, Int, Float, String };

pub struct RefinementContext<'z3, 'c> {
    z3_context: &'z3 z3::Context,
    pub solver: z3::Solver<'z3>,
    pub definitions: HashMap<DefinitionInfoId, Refinements<'z3, 'c>>,
    pub types: HashMap<Type, z3::Sort<'z3>>,
}

pub type Z3Ast<'z3> = z3::ast::Dynamic<'z3>;
pub type Z3Bool<'z3> = z3::ast::Bool<'z3>;
type Z3Int<'z3> = z3::ast::Int<'z3>;

impl<'z3, 'c> RefinementContext<'z3, 'c> {
    pub fn new(z3_context: &'z3 z3::Context) -> Self {
        RefinementContext { 
            z3_context,
            solver: z3::Solver::new(z3_context),
            definitions: HashMap::new(),
            types: HashMap::new(),
        }
    }

    pub fn value<Ast: Into<Z3Ast<'z3>>>(ast: Ast) -> Refinements<'z3, 'c> {
         Refinements::new(ast.into())
    }

    pub fn bool_value(&self, value: bool) -> Refinements<'z3, 'c> {
        Self::value(Bool::from_bool(self.z3_context, value))
    }

    pub fn integer_value(&self, value: u64, signed: bool) -> Refinements<'z3, 'c> {
        let value = if signed {
            Int::from_i64(self.z3_context, value as i64)
        } else {
            Int::from_u64(self.z3_context, value)
        };
        Self::value(value)
    }

    pub fn float_value(&self, value: f64) -> Refinements<'z3, 'c> {
        Self::value(Float::from_f64(self.z3_context, value))
    }

    pub fn string_value(&self, value: &str) -> Refinements<'z3, 'c> {
        Self::value(String::from_str(self.z3_context, value).unwrap())
    }

    pub fn variable(&self, name: &str, sort: z3::Sort<'z3>) -> Z3Ast<'z3> {
        z3::FuncDecl::new(self.z3_context, name, &[], &sort).apply(&[])
    }

    pub fn type_to_sort(&mut self, typ: &Type, cache: &ModuleCache<'c>) -> z3::Sort<'z3> {
        use crate::types::Type::*;
        match typ {
            Primitive(primitive) => self.primitive_type_to_sort(primitive, cache),

            Function(args, return_type, varargs) => self.function_to_sort(typ, &return_type, args, *varargs, cache),

            TypeVariable(id) => {
                match cache.find_binding(*id) {
                    Some(binding) => self.type_to_sort(binding, cache),
                    None => z3::Sort::int(self.z3_context), // TODO: Can we get away with translating generic params into ints?
                }
            },

            UserDefinedType(id) => {
                if let Some(sort) = self.types.get(&typ) {
                    return sort.clone();
                }

                self.user_defined_type_to_sort(&typ, *id, vec![], cache)
            }

            TypeApplication(typ, args) => self.type_application_to_sort(typ, args, cache),

            Ref(_) => {
                unreachable!("Kind error during refinement type inference. Attempted to translate a `ref` without a type argument into a z3::Sort")
            },

            ForAll(_, typ) => self.type_to_sort(typ, cache),
        }
    }

    fn primitive_type_to_sort(&mut self, typ: &PrimitiveType, _cache: &ModuleCache<'c>) -> z3::Sort<'z3> {
        use types::PrimitiveType::*;
        match typ {
            IntegerType(_) => z3::Sort::int(self.z3_context),
            FloatType => z3::Sort::double(self.z3_context),
            CharType => z3::Sort:: int(self.z3_context), // TODO: Should Char/Unit be None?
            BooleanType => z3::Sort::bool(self.z3_context),
            UnitType => z3::Sort::bool(self.z3_context),
        }
    }

    fn function_to_sort(&mut self, typ: &Type, return_type: &Type,
        args: &[Type], varargs: bool, cache: &ModuleCache<'c>) -> z3::Sort<'z3>
    {
        // no function sort in z3, use an uninterpreted sort instead
        let args = fmap(args, |arg| cache.follow_bindings(arg));
        let return_type = cache.follow_bindings(return_type);

        if let Some(sort) = self.types.get(&typ) {
            return sort.clone();
        }

        let name = typ.display(cache).to_string();
        let sort = z3::Sort::uninterpreted(self.z3_context, z3::Symbol::String(name));
        let typ = Type::Function(args, Box::new(return_type), varargs);
        self.types.insert(typ, sort.clone());
        sort
    }

    fn type_application_to_sort(&mut self, typ: &Type, args: &[Type], cache: &ModuleCache<'c>) -> z3::Sort<'z3> {
        let args = fmap(args, |arg| cache.follow_bindings(arg));
        let typ = cache.follow_bindings(typ);

        match &typ {
            Type::Ref(_) => {
                assert_eq!(args.len(), 1);
                let name = format!("ref_{}", args[0].display(cache));

                let typ = Type::TypeApplication(Box::new(typ), args);
                if let Some(sort) = self.types.get(&typ) {
                    return sort.clone();
                }

                let sort = z3::Sort::uninterpreted(self.z3_context, z3::Symbol::String(name));
                self.types.insert(typ, sort.clone());
                sort
            },
            Type::UserDefinedType(id) => self.user_defined_type_to_sort(&typ, *id, args, cache),
            _ => {
                unreachable!("Type {} requires 0 type args but was applied to {:?}", typ.display(cache), args);
            }
        }
    }

    fn user_defined_type_to_sort(&mut self, typ: &Type, id: TypeInfoId, args: Vec<Type>, cache: &ModuleCache<'c>) -> z3::Sort<'z3> {
        if let Some(sort) = self.types.get(&typ) {
            return sort.clone();
        }

        let name = typ.display(cache).to_string();
        let info = &cache.type_infos[id.0];

        // TODO: We may need to handle monomorphisation mappings in these translations
        let sort = match &info.body {
            TypeInfoBody::Union(variants) => {
                self.sum_type_to_sort(&name, variants, cache)
            },
            TypeInfoBody::Struct(fields, id) => {
                let mut field_accessors = vec![];
                let mut field_vars = vec![];

                for field in fields {
                    let sort = self.type_to_sort(&field.field_type, cache);
                    let name: &str = &field.name;
                    field_vars.push(self.variable(name, sort.clone()));
                    field_accessors.push((name, z3::DatatypeAccessor::Sort(sort)))
                }

                let datatype = z3::DatatypeBuilder::new(self.z3_context, name.clone())
                    .variant(&name, field_accessors)
                    .finish();

                let constructor = Refinements::function(datatype.variants[0].constructor.clone(), field_vars);
                self.definitions.insert(*id, constructor);
                datatype.sort
            },
            TypeInfoBody::Alias(typ) => self.type_to_sort(typ, cache),
            TypeInfoBody::Unknown => unreachable!("info.body of {} is unknown", name),
        };

        self.types.insert(typ.clone(), sort.clone());
        sort
    }

    fn sum_type_to_sort(&mut self, typename: &str, variants: &[TypeConstructor<'c>], cache: &ModuleCache<'c>) -> z3::Sort<'z3> {
        let mut builder = z3::DatatypeBuilder::new(self.z3_context, typename.to_string());
        let mut ids_and_fields = vec![];

        // TODO: using the high-level z3 api is painful here - it forces us to use two loops.
        // investigate if using z3_sys here would allow us to do the same thing in fewer lines.
        for variant in variants {
            let field_names: Vec<_> = variant.args.iter().enumerate().map(|(i, _)| {
                format!("{}${}${}", typename, variant.name, i)
            }).collect();

            let mut field_vars = vec![];

            let fields = variant.args.iter().enumerate().map(|(i, field)| {
                let sort = self.type_to_sort(&field, cache);
                let name: &str = &field_names[i];
                field_vars.push(self.variable(name, sort.clone()));
                (name, z3::DatatypeAccessor::Sort(sort))
            }).collect();

            let name = format!("{}${}", typename, variant.name);
            builder = builder.variant(&name, fields);
            ids_and_fields.push((variant.id, field_vars));
        }

        let datatype = builder.finish();
        for (variant, (constructor_id, field_vars)) in datatype.variants.iter().zip(ids_and_fields) {
            let constructor = Refinements::function(variant.constructor.clone(), field_vars);
            self.definitions.insert(constructor_id, constructor);
        }
        datatype.sort
    }

    pub fn refine_pattern(&mut self, ast: &ast::Ast<'c>, cache: &ModuleCache<'c>) -> (Refinements<'z3, 'c>, Vec<DefinitionInfoId>) {
        use ast::Ast::*;
        match ast {
            Literal(literal) => {
                (literal.refine(self, cache), vec![])
            },
            Variable(variable) => {
                let id = variable.definition.unwrap();
                // if let Some(refinements) = self.definitions.get(&id) {
                //     return refinements.clone();
                // }

                // let mut refinements = self.refine_definition(id, cache);
                let sort = self.type_to_sort(variable.typ.as_ref().unwrap(), cache);
                let name = variable.to_string();
                let var = self.variable(&format!("{}${}", name, id.0), sort);
                let refinements = Refinements::new(var);
                self.definitions.insert(id, refinements.clone());
                (refinements, vec![id])
            },
            TypeAnnotation(annotation) => {
                self.refine_pattern(annotation.lhs.as_ref(), cache)
            },
            FunctionCall(call) => {
                let f = call.function.refine(self, cache);
                match f.get_func_decl() {
                    Some((decl, _)) => {
                        let mut refinements = Refinements::none();
                        let mut args = vec![];
                        let mut ids = vec![];

                        for arg in call.args.iter() {
                            let (arg_refinements, mut arg_ids) = self.refine_pattern(arg, cache);
                            args.push(arg_refinements.get_value().unwrap());
                            ids.append(&mut arg_ids);
                            refinements = refinements.combine(arg_refinements);
                        }

                        let arg_refs: Vec<_> = args.iter().collect();
                        let callval = decl.apply(&arg_refs);
                        (refinements.set_return(callval), ids)
                    }
                    None => { // TODO
                        (Refinements::none(), vec![])
                    }
                }
            },
            _ => {
                unreachable!("Found invalid expr in pattern: {}", ast);
            }
        }
    }

    pub fn refine_definition(&mut self, id: DefinitionInfoId, typ: &Type, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        if let Some(refinements) = self.definitions.get(&id) {
            return refinements.clone();
        }

        let info = &cache.definition_infos[id.0];
        let typ = cache.follow_bindings(typ);

        if let Some(refinements) = self.check_builtin(id, info, &typ) {
            return refinements
        }

        // Add the definition to our known definitions before we actually compile
        // the DefinitionKind below, otherwise we would recurse forever if the
        // definition references itself.
        let sort = self.type_to_sort(info.typ.as_ref().unwrap(), cache);
        let variable = self.variable(&format!("{}${}", info.name, id.0), sort);
        let refinements = Refinements::new(variable.clone());
        self.definitions.insert(id, refinements.clone());

        let definition_refinements = match &info.definition {
            Some(DefinitionKind::Definition(definition)) => definition.refine(self, cache),
            Some(DefinitionKind::TypeConstructor { .. }) => {
                self.type_to_sort(info.typ.as_ref().unwrap(), cache);
                self.definitions.get(&id).cloned().unwrap()
            },
            Some(DefinitionKind::Extern(_)) => Refinements::Impure,
            Some(DefinitionKind::TraitDefinition(_)) => Refinements::none(),
            Some(DefinitionKind::Parameter) => Refinements::none(),
            Some(DefinitionKind::MatchPattern) => Refinements::none(),
            None => unreachable!("No definition for {}", info.name),
        };

        let refinements = definition_refinements.set_return(variable);
        self.definitions.insert(id, refinements.clone());
        refinements
    }

    pub fn define_function(&mut self, name: &str, parameters: Vec<Refinements<'z3, 'c>>,
        given_clause: Option<Refinements<'z3, 'c>>,
        body: Refinements<'z3, 'c>, location: Location<'c>) -> Refinements<'z3, 'c>
    {
        let body_value = body.get_value();
        match (body_value, body) {
            (_, Refinements::Impure) => Refinements::Impure,
            (Some(body_value), Refinements::Pure { asserts, .. }) => {
                let range = body_value.get_sort();

                let mut body = Refinements::with_asserts(asserts);
                let mut domain = vec![];
                let mut param_values = vec![];
                for parameter in parameters {
                    let value = parameter.get_value().unwrap();
                    domain.push(value.get_sort());
                    param_values.push(value);

                    if let Refinements::Pure { asserts, .. } = parameter {
                        body = body.add_asserts(asserts);
                    }
                }

                let param_refs: Vec<_> = param_values.iter().collect();
                let domain_refs: Vec<_> = domain.iter().collect();

                let decl = z3::FuncDecl::new_recursive(self.z3_context, name, &domain_refs, &range);
                decl.set_body(&param_refs, &body_value);

                Refinements::function(decl, param_values)
                    .combine(body)
                    .try_add_assert(given_clause, location)
            }
            (None, refinements) => refinements,
        }
    }

    pub fn bind(&mut self, definitions: &[DefinitionInfoId], pattern: Refinements<'z3, 'c>, value: Refinements<'z3, 'c>) {
        let binding = pattern.bind_to(&self.solver, value);

        for definition in definitions {
            self.definitions.entry(*definition).and_modify(|entry| {
                *entry = binding.clone().combine(entry.clone())
            });
        }
    }

    pub fn check_builtin(&mut self, id: DefinitionInfoId, definition: &DefinitionInfo, typ: &Type) -> Option<Refinements<'z3, 'c>> {
        let args = match typ {
            Type::Function(params, ..) => params,
            _ => return None,
        };

        use Type::Primitive;
        use PrimitiveType::*;
        use crate::lexer::token::Token;
        match args.as_slice() {
            [Primitive(IntegerType(_)), Primitive(IntegerType(_))] => {
                let name = format!("{}${}", definition.name, id.0);

                if definition.name == Token::Add.to_string() {
                    return self.make_builtin(&name, "a", "b", |c, a, b| Int::add(c, &[a, b]).into());
                } else if definition.name == Token::Subtract.to_string() {
                    return self.make_builtin(&name, "c", "d", |c, a, b| Int::sub(c, &[a, b]).into());
                } else if definition.name == Token::Multiply.to_string() {
                    return self.make_builtin(&name, "e", "f", |c, a, b| Int::mul(c, &[a, b]).into());
                } else if definition.name == Token::Divide.to_string() {
                    return self.make_builtin(&name, "g", "h", |_, a, b| a.div(b).into());
                } else if definition.name == Token::LessThan.to_string() {
                    return self.make_builtin(&name, "i", "j", |_, a, b| a.lt(b).into());
                } else if definition.name == Token::LessThanOrEqual.to_string() {
                    return self.make_builtin(&name, "k", "l", |_, a, b| a.le(b).into());
                } else if definition.name == Token::GreaterThan.to_string() {
                    return self.make_builtin(&name, "m", "n", |_, a, b| a.gt(b).into());
                } else if definition.name == Token::GreaterThanOrEqual.to_string() {
                    return self.make_builtin(&name, "o", "p", |_, a, b| a.ge(b).into());
                } else if definition.name == Token::EqualEqual.to_string() {
                    return self.make_builtin(&name, "q", "r", |_, a, b| a._eq(b).into());
                } else if definition.name == Token::NotEqual.to_string() {
                    return self.make_builtin(&name, "s", "t", |c, a, b| Z3Ast::distinct(c, &[&a.to_owned().into(), &b.to_owned().into()]).into());
                }
            },
            _ => (),
        }

        None
    }

    fn make_builtin<F>(&self, name: &str, param1: &str, param2: &str, f: F) -> Option<Refinements<'z3, 'c>>
        where F: FnOnce(&'z3 z3::Context, &Z3Int<'z3>, &Z3Int<'z3>) -> Z3Ast<'z3>
    {
        let a = Int::new_const(self.z3_context, param1);
        let b = Int::new_const(self.z3_context, param2);
        let body = f(self.z3_context, &a, &b);
        let arg_sort = a.get_sort();
        let ret_sort = body.get_sort();

        let (a, b) = (a.into(), b.into());
        let f = z3::FuncDecl::new_recursive(self.z3_context, name, &[&arg_sort, &arg_sort], &ret_sort);
        f.set_body(&[&a, &b], &body.into());
        return Some(Refinements::function(f, vec![a, b]));
    }
}
