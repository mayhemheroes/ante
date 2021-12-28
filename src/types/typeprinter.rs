//! typeprinter.rs - Utilities for printing out types and traits.
//! Since a type may contain TypeVariables with their TypeBindings in the cache,
//! printing out a bound type requires using the cache as well. Resultingly,
//! types/traits are displayed via `type.display(cache)` rather than directly having
//! a Display impl.
use crate::types::{ Type, TypeVariableId, TypeInfoId, PrimitiveType,
                    FunctionType, TypeBinding };
use crate::types::traits::{ RequiredTrait, RequiredTraitPrinter };
use crate::types::typechecker::find_all_typevars;
use crate::refinements::types::Refinement;
use crate::cache::{ ModuleCache, DefinitionInfoId };
use crate::util::{ join_with, reinterpret_from_bits };

use std::collections::{ HashMap, HashSet };
use std::fmt::{ Display, Debug, Formatter };

use colored::*;

/// Wrapper containing the information needed to print out a type
pub struct TypePrinter<'a, 'b> {
    typ: &'a Type,

    /// Maps unique type variable IDs to human readable names like a, b, c, etc.
    typevar_names: HashMap<TypeVariableId, String>,

    /// Maps unique DefinitionInfoIds to their actual names from the module cache
    /// or a unique one in case two ever collide.
    variable_names: HashMap<DefinitionInfoId, String>,

    /// Controls whether to show or hide some hidden data, like ref lifetimes
    debug: bool,

    cache: &'a ModuleCache<'b>
}

impl<'a, 'b> Display for TypePrinter<'a, 'b> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.fmt_type(&self.typ, f)
    }
}

impl<'a, 'b> Debug for TypePrinter<'a, 'b> {
    fn fmt(&self, f: &mut Formatter) -> std::fmt::Result {
        self.fmt_type(&self.typ, f)
    }
}

/// Fill a HashMap with human readable names for each typevar in the given Vec.
/// For example, given [TypeVariableId(53), TypeVariableId(92)] this may yield `a` and `b`
/// respectively.
fn fill_typevar_map(map: &mut HashMap<TypeVariableId, String>, typevars: Vec<TypeVariableId>, current: &mut char) {
    for typevar in typevars {
        if !map.contains_key(&typevar) {
            map.insert(typevar, current.to_string());
            *current = (*current as u8 + 1) as char;
            assert!(*current != 'z'); // TODO: wrap to aa, ab, ac...
        }
    }
}

pub fn variable_name_map<'c>(vars: Vec<DefinitionInfoId>, cache: &ModuleCache<'c>) -> HashMap<DefinitionInfoId, String> {
    let mut map = HashMap::new();
    let mut used_names = HashSet::new();

    for id in vars {
        if !map.contains_key(&id) {
            let basename = &cache.definition_infos[id.0].name;

            let mut name = basename.clone();
            let mut counter = 2;
            while used_names.contains(&name) {
                name = format!("{}{}", basename, counter);
                counter += 1;
            }

            used_names.insert(name.clone());
            map.insert(id, name);
        }
    }
    map
}

/// Prints out the given type and traits on screen. The type and traits are all taken in together
/// so that any repeated typevariables e.g. `TypeVariableId(55)` that may be used in both the type
/// and any traits are given the same name in both. Printing out the type separately from the
/// traits would cause type variable naming to restart at `a` which may otherwise give them
/// different names.
pub fn show_type_and_traits<'b>(typ: &Type, traits: &[RequiredTrait], cache: &ModuleCache<'b>) {
    let mut typevar_map = HashMap::new();
    let mut current = 'a';

    let (typevars, vars) = find_all_typevars(typ, false, cache);
    fill_typevar_map(&mut typevar_map, typevars, &mut current);
    
    let variable_names = variable_name_map(vars, cache);

    let debug = true;
    print!("{}", TypePrinter { typ, cache, debug, variable_names, typevar_names: typevar_map.clone() });

    let mut traits = traits.iter().map(|required_trait| {
        let (typevars, variables) = required_trait.find_all_typevars(cache);
        fill_typevar_map(&mut typevar_map, typevars, &mut current);

        let variable_names = variable_name_map(variables, cache);
        RequiredTraitPrinter { required_trait: required_trait.clone(), variable_names, cache, debug, typevar_names: typevar_map.clone() }
            .to_string()
    }).collect::<Vec<String>>();

    // Remove "duplicate" traits so users don't see `given Add a, Add a`.
    // These contain usage information that is different within them but this
    // isn't used in their Display impl so they look like duplicates.
    traits.sort();
    traits.dedup();

    if !traits.is_empty() {
        print!("\n  given {}", join_with(&traits, ", "));
    }

    println!("");
}

impl<'a, 'b> TypePrinter<'a, 'b> {
    pub fn new(typ: &'a Type, typevar_names: HashMap<TypeVariableId, String>, variable_names: HashMap<DefinitionInfoId, String>, debug: bool, cache: &'a ModuleCache<'b>) -> TypePrinter<'a, 'b> {
        TypePrinter { typ, typevar_names, variable_names, debug, cache }
    }

    fn fmt_type(&self, typ: &Type, f: &mut Formatter) -> std::fmt::Result {
        match typ {
            Type::Primitive(primitive) => self.fmt_primitive(primitive, f),
            Type::Function(function) => self.fmt_function(function, f),
            Type::TypeVariable(id) => self.fmt_type_variable(*id, f),
            Type::UserDefinedType(id) => self.fmt_user_defined_type(*id, f),
            Type::TypeApplication(constructor, args) => self.fmt_type_application(constructor, args, f),
            Type::Ref(lifetime) => self.fmt_ref(*lifetime, f),
            Type::ForAll(typevars, typ) => self.fmt_forall(typevars, typ, f),
            Type::Refined(typ, refinements) => self.fmt_refined(typ, refinements, f),
            Type::Named(id, typ) => self.fmt_named(*id, typ, f),
        }
    }

    fn fmt_primitive(&self, primitive: &PrimitiveType, f: &mut Formatter) -> std::fmt::Result {
        match primitive {
            PrimitiveType::IntegerType(kind) => write!(f, "{}", kind.to_string().blue()),
            PrimitiveType::FloatType => write!(f, "{}", "float".blue()),
            PrimitiveType::CharType => write!(f, "{}", "char".blue()),
            PrimitiveType::BooleanType => write!(f, "{}", "bool".blue()),
            PrimitiveType::UnitType => write!(f, "{}", "unit".blue()),
            PrimitiveType::Ptr => write!(f, "{}", "Ptr".blue()),
        }
    }

    fn fmt_function(&self, function: &FunctionType, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}", "(".blue())?;
        for (i, param) in function.parameters.iter().enumerate() {
            self.fmt_type(param, f)?;
            write!(f, " ")?;

            if i != function.parameters.len() - 1 {
                write!(f, "{}", "-> ".blue())?;
            }
        }

        if function.is_varargs {
            write!(f, "{}", "... ".blue())?;
        }

        if function.environment.is_unit(&self.cache) {
            write!(f, "{}", "-> ".blue())?;
        } else {
            write!(f, "{}", "=> ".blue())?;
        }

        self.fmt_type(function.return_type.as_ref(), f)?;
        write!(f, "{}", ")".blue())
    }

    fn fmt_type_variable(&self, id: TypeVariableId, f: &mut Formatter) -> std::fmt::Result {
        match &self.cache.type_bindings[id.0] {
            TypeBinding::Bound(typ) => self.fmt_type(typ, f),
            TypeBinding::Unbound(..) => {
                let default = "?".to_string();
                let name = self.typevar_names.get(&id).unwrap_or(&default).blue();
                write!(f, "{}", name)
            }
        }
    }

    fn fmt_user_defined_type(&self, id: TypeInfoId, f: &mut Formatter) -> std::fmt::Result {
        let name = self.cache.type_infos[id.0].name.blue();
        write!(f, "{}", name)
    }

    fn fmt_type_application(&self, constructor: &Box<Type>, args: &Vec<Type>, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}", "(".blue())?;

        if constructor.is_pair_type() {
            self.fmt_pair(args, f)?;
        } else {
            self.fmt_type(constructor.as_ref(), f)?;
            for arg in args.iter() {
                write!(f, " ")?;
                self.fmt_type(arg, f)?;
            }
        }

        write!(f, "{}", ")".blue())
    }

    fn fmt_pair(&self, args: &Vec<Type>, f: &mut Formatter) -> std::fmt::Result {
        assert_eq!(args.len(), 2);

        self.fmt_type(&args[0], f)?;

        write!(f, "{}", ", ".blue())?;

        match &args[1] {
            Type::TypeApplication(constructor, args) if constructor.is_pair_type() => {
                self.fmt_pair(args, f)
            },
            other => self.fmt_type(other, f)
        }
    }

    fn fmt_ref(&self, lifetime: TypeVariableId, f: &mut Formatter) -> std::fmt::Result {
        match &self.cache.type_bindings[lifetime.0] {
            TypeBinding::Bound(typ) => self.fmt_type(typ, f),
            TypeBinding::Unbound(..) => {
                write!(f, "{}", "ref".blue())?;

                if self.debug {
                    match self.typevar_names.get(&lifetime) {
                        Some(name) => write!(f, "{{{}}}", name)?,
                        None => write!(f, "{{?{}}}", lifetime.0)?,
                    }
                }
                Ok(())
            }
        }
    }

    fn fmt_forall(&self, typevars: &Vec<TypeVariableId>, typ: &Box<Type>, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}", "(forall".blue())?;
        for typevar in typevars.iter() {
            write!(f, " ")?;
            self.fmt_type_variable(*typevar, f)?;
        }
        write!(f, "{}", ". ".blue())?;
        self.fmt_type(typ.as_ref(), f)?;
        write!(f, "{}", ")".blue())
    }

    fn fmt_refined(&self, typ: &Box<Type>, refinement: &Refinement, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}", "(".blue())?;
        self.fmt_type(typ, f)?;
        write!(f, "{}", " & ".blue())?;
        self.fmt_refinement(refinement, f)?;
        write!(f, "{}", ")".blue())
    }

    fn fmt_refinement(&self, refinement: &Refinement, f: &mut Formatter) -> std::fmt::Result {
        match refinement {
            Refinement::Integer(x) => write!(f, "{}", *x),
            Refinement::Float(x) => write!(f, "{}", reinterpret_from_bits(*x)),
            Refinement::Variable(id) => write!(f, "{}", self.variable_names[id]),
            Refinement::Uninterpreted(id, args)
            | Refinement::Constructor(id, args) => {
                write!(f, "({}", self.variable_names[id])?;
                for arg in args.iter() {
                    write!(f, " ")?;
                    self.fmt_refinement(arg, f)?;
                }
                write!(f, ")")
            },
            Refinement::PrimitiveCall(prim, args) => {
                write!(f, "(")?;
                if args.len() == 1 {
                    write!(f, "{} ", prim)?;
                    self.fmt_refinement(&args[0], f)?;
                } else {
                    assert_eq!(args.len(), 2);
                    self.fmt_refinement(&args[0], f)?;
                    write!(f, " {} ", prim)?;
                    self.fmt_refinement(&args[1], f)?;
                }
                write!(f, ")")
            },
            Refinement::Boolean(b) => write!(f, "{}", *b),
            Refinement::Unit => write!(f, "()"),
            Refinement::Forall(x, t, e) => {
                write!(f, "forall {}:{:?}. ", self.variable_names[x], t)?;
                self.fmt_refinement(e.as_ref(), f)
            }
        }
    }

    fn fmt_named(&self, id: DefinitionInfoId, typ: &Box<Type>, f: &mut Formatter) -> std::fmt::Result {
        write!(f, "{}{}: ", "(".blue(), self.variable_names[&id])?;
        self.fmt_type(typ, f)?;
        write!(f, "{}", ")".blue())
    }
}
