use crate::parser::ast;
use crate::cache::ModuleCache;
use crate::util::{ fmap, reinterpret_from_bits };

mod context;
mod refinements;

use crate::refine::context::RefinementContext;
use crate::refine::refinements::{ Refinements, RefinementValue };

use z3::ast::Ast;

pub fn refine<'c>(ast: &ast::Ast<'c>, output_refinements: bool, cache: &ModuleCache<'c>) {
    let z3_context = z3::Context::new(&z3::Config::new());
    let mut context = RefinementContext::new(&z3_context);
    let refinements = ast.refine(&mut context, cache);

    if output_refinements {
        println!("{}", refinements);
    }

    let solver = context.solver;

    if let Refinements::Pure { asserts, .. } = refinements {
        for assert in asserts {
            // We must push and pop asserts each time otherwise the
            // first unsat result will cause all following results to be unsat
            solver.push();
            solver.assert(&assert.0.not());
            match solver.check() {
                z3::SatResult::Sat => {
                    let model = solver.get_model();
                    let counter_example = match model {
                        Some(model) => format!("Counter-example is {}", model),
                        None => "(No counter-example)".to_string(),
                    };
                    error!(assert.1, "Failed to prove {}. {}", assert.0, counter_example);
                },
                z3::SatResult::Unsat => {},
                z3::SatResult::Unknown => {
                    println!("Query was interrupted, timed out or failed: {}", solver.get_reason_unknown().unwrap());
                }
            }
            solver.pop(1);
        }
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
            LiteralKind::Char(_) => Refinements::none(),
            LiteralKind::Bool(b) => context.bool_value(*b),
            LiteralKind::Float(f) => context.float_value(reinterpret_from_bits(*f)),
            LiteralKind::Integer(i, kind) => context.integer_value(*i, kind.is_signed(cache)),
            LiteralKind::String(s) => context.string_value(s),
            LiteralKind::Unit => Refinements::none(),
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

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Lambda<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let refinements = self.body.refine(context, cache);
        let parameters = fmap(&self.args, |parameter| {
            context.refine_pattern(parameter, cache).0
        });

        let asserts = self.given.as_ref().map(|given| {
            given.refine(context, cache)
        });

        context.define_function("lambda", parameters, asserts, refinements, self.location)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::FunctionCall<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let mut f = self.function.refine(context, cache);
        let args = fmap(&self.args, |arg| arg.refine(context, cache));

        match &f {
            Refinements::Pure { value: RefinementValue::Function(func), .. } => {
                let func = func.1.clone();
                let replacements: Vec<_> = func.iter().zip(args).collect();
                f.substitute(replacements, self.location)
            },
            _ => {
                // We don't know what function we're applying (it may be higher-order) so just push
                // all the bindings and asserts and set the result as unrepresentable.
                for arg in args {
                    f = f.combine(arg);
                }
                f.set_unrepresentable()
            }
        }
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Definition<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let (lhs, ids) = context.refine_pattern(self.pattern.as_ref(), cache);
        let rhs = self.expr.refine(context, cache);
        context.bind(&ids, lhs, rhs);
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::If<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let cond = self.condition.refine(context, cache);
        let then = self.then.refine(context, cache);

        let mut refinements = cond.clone().implies(then);

        if let Some(otherwise) = self.otherwise.as_ref() {
            let otherwise = otherwise.refine(context, cache);

            let not = cond.map_value(|cond| cond.as_bool().unwrap().not().into());
            let otherwise = not.implies(otherwise);

            refinements = refinements.combine(otherwise);
        }

        refinements.set_unrepresentable()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Match<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        let mut refinements = Refinements::none();

        let match_expr = self.expression.refine(context, cache);

        for (pattern, branch) in self.branches.iter() {
            let pattern = pattern.refine(context, cache);
            let eq = pattern.map(|pattern, asserts| {
                let pattern_match = match_expr.clone().map_value(|value| value._eq(&pattern).into());
                pattern_match.add_asserts(asserts)
            });

            let branch = branch.refine(context, cache);
            let branch = eq.implies(branch);
            refinements = refinements.combine(branch);
        }

        refinements.set_unrepresentable()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TypeDefinition<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TypeAnnotation<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        self.lhs.refine(context, cache)
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Import<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TraitDefinition<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::TraitImpl<'c> {
    fn refine(&self, context: &mut RefinementContext<'z3, 'c>, cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        for definition in self.definitions.iter() {
            // TODO: verify any assertions, check that nothing should bubble up
            definition.refine(context, cache);
        }

        Refinements::none()
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
        let mut refinements = Refinements::none();

        for statement in self.statements.iter() {
            let more = statement.refine(context, cache);
            refinements = refinements.combine(more);
        }

        refinements
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Extern<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::MemberAccess<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        // TODO lookup datatype accessor
        Refinements::none()
    }
}

impl<'z3, 'c> Refineable<'z3, 'c> for ast::Assignment<'c> {
    fn refine(&self, _context: &mut RefinementContext<'z3, 'c>, _cache: &ModuleCache<'c>) -> Refinements<'z3, 'c> {
        Refinements::Impure
    }
}
