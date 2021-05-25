use crate::parser::ast;
use crate::cache::ModuleCache;
use crate::util::{ fmap, reinterpret_from_bits };

mod context;
mod refinements;
mod model_parser;

use crate::refine::context::RefinementContext;
use crate::refine::refinements::{ Refinements, RefinementValue };

use z3::ast::Ast;

pub fn refine<'c>(ast: &ast::Ast<'c>, output_refinements: bool, cache: &ModuleCache<'c>) {
    let z3_context = z3::Context::new(&z3::Config::new());
    let mut context = RefinementContext::new(&z3_context);
    let refinements = ast.refine(&mut context, cache);

    if output_refinements {
        context.output_refinements(cache);
    }

    for binding in &refinements.bindings {
        context.solver.assert(binding);
    }

    for assert in refinements.asserts {
        // We must push and pop asserts each time otherwise the
        // first unsat result will cause all following results to be unsat
        context.solver.push();
        context.solver.assert(&assert.0.not());
        match context.solver.check() {
            z3::SatResult::Sat => {
                context.issue_refinement_error(&assert.0, context.solver.get_model(), cache, assert.1, assert.2);
            },
            z3::SatResult::Unsat => {},
            z3::SatResult::Unknown => {
                error!(assert.1, "error while solving {}: {}", assert.0, context.solver.get_reason_unknown().unwrap());
            }
        }
        context.solver.pop(1);
    }
}

pub trait Refineable<'z3, 'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c>;
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Ast<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        dispatch_on_expr!(self, Refineable::refine, context, cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Literal<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        use crate::parser::ast::LiteralKind;
        match &self.kind {
            LiteralKind::Char(_) => context.unrepresentable(self.typ.as_ref().unwrap(), cache),
            LiteralKind::Bool(b) => context.bool_value(*b),
            LiteralKind::Float(f) => context.float_value(reinterpret_from_bits(*f)),
            LiteralKind::Integer(i, kind) => context.integer_value(*i, kind.is_signed(cache)),
            LiteralKind::String(s) => context.string_value(s),
            LiteralKind::Unit => context.unrepresentable(self.typ.as_ref().unwrap(), cache),
        }
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Variable<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let definition_id = self.definition.unwrap();

        match context.definitions.get(&definition_id) {
            Some(refinements) => refinements.clone(),
            None => context.refine_definition(definition_id, self.typ.as_ref().unwrap(), cache),
        }
    }
}

fn refine_lambda<'z3, 'c>(lambda: &ast::Lambda<'c>, name: &str,
    context: &mut RefinementContext<'z3, 'c>,
    cache: &ModuleCache<'c>) -> Refinements<'z3, 'c>
{
    let parameters = fmap(&lambda.args, |parameter| {
        context.refine_pattern(parameter, cache).0
    });

    let asserts = lambda.given.as_ref().map(|given| {
        given.refine(context, cache)
    });

    let refinements = lambda.body.refine(context, cache);
    context.define_function(name, parameters, asserts, refinements, lambda.location)
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Lambda<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let name = format!("lambda@{:?}:{}:{}", self.location.filename, self.location.start.line, self.location.start.column);
        refine_lambda(self, &name, context, cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::FunctionCall<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let f = self.function.refine(context, cache);
        let args = fmap(&self.args, |arg| arg.refine(context, cache));

        match &f.value {
            RefinementValue::Function(func) => {
                let func = func.1.clone();
                let replacements: Vec<_> = func.iter().zip(args).collect();
                f.substitute(replacements, self.location)
            },
            _ => {
                let args = Refinements::combine_all(args.into_iter());
                
                context.unrepresentable(self.typ.as_ref().unwrap(), cache)
                    .combine(f)
                    .combine(args)
            }
        }
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Definition<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let (lhs, ids) = context.refine_pattern(self.pattern.as_ref(), cache);

        let rhs = match self.expr.as_ref() {
            ast::Ast::Lambda(lambda) => {
                assert_eq!(ids.len(), 1);
                let info = &cache.definition_infos[ids[0].0];
                let name = format!("{}${}", info.name, ids[0].0);
                refine_lambda(lambda, &name, context, cache)
            },
            expr => expr.refine(context, cache),
        };

        context.bind(&ids, lhs, rhs);
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::If<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let cond = self.condition.refine(context, cache);
        let then = self.then.refine(context, cache);

        let (mut asserts, mut bindings) = cond.implies(then);

        if let Some(otherwise) = self.otherwise.as_ref() {
            let otherwise = otherwise.refine(context, cache);

            let not = cond.map_value(|cond| cond.as_bool().unwrap().not().into());
            let mut otherwise = not.implies(otherwise);

            asserts.append(&mut otherwise.0);
            bindings.append(&mut otherwise.1);
        }

        let value = context.unrepresentable_value(self.typ.as_ref().unwrap(), cache);
        Refinements::new(value, asserts, bindings)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Match<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let mut asserts = vec![];
        let mut bindings = vec![];
        let match_expr = self.expression.refine(context, cache);

        let mut previous_cases = vec![];

        for (pattern, branch) in self.branches.iter() {
            let pattern = pattern.refine(context, cache);
            let branch = branch.refine(context, cache);

            match (&pattern.value, &match_expr.value) {
                (RefinementValue::Pure(pattern_value), RefinementValue::Pure(value)) => {
                    let eq = value._eq(pattern_value);
                    previous_cases.push(eq.clone());

                    let ret = if previous_cases.len() == 1 {
                        eq.clone()
                    } else {
                        let cases = previous_cases.iter().collect::<Vec<_>>();
                        z3::ast::Bool::and(context.z3_context, &cases)
                    };

                    let pattern_matches = pattern.set_return(ret.into());

                    // Future cases will know the value didn't match the previous patterns
                    previous_cases.pop();
                    previous_cases.push(eq.not());

                    let mut branch_matched = pattern_matches.implies(branch);
                    asserts.append(&mut branch_matched.0);
                    bindings.append(&mut branch_matched.1);
                },
                _ => (),
            }
        }

        let value = context.unrepresentable_value(self.typ.as_ref().unwrap(), cache);
        Refinements::new(value, asserts, bindings)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TypeDefinition<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TypeAnnotation<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        self.lhs.refine(context, cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Import<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TraitDefinition<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TraitImpl<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        for definition in self.definitions.iter() {
            // TODO: verify any assertions, check that nothing should bubble up
            definition.refine(context, cache);
        }

        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Return<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        // TODO: Handle early returns
        self.expression.refine(context, cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Sequence<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::combine_all(
            self.statements.iter()
                .map(|statement| statement.refine(context, cache))
        )
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Extern<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::MemberAccess<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        // TODO lookup datatype accessor
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Assignment<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::new(RefinementValue::Impure, vec![], vec![])
    }
}
