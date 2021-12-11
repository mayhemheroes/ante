use crate::parser::ast;
use crate::cache::ModuleCache;
use crate::error::location::Location;
use crate::refinements::context::RefinementContext;
use crate::types::Type;
use crate::types::refinement::{ self, Refinement };
use crate::util::{ fmap, reinterpret_from_bits };

mod context;

pub fn refine<'c>(ast: &ast::Ast<'c>, output_refinements: bool, cache: &ModuleCache<'c>) {
    let mut context = RefinementContext::new();
    let refinements = ast.refine(&mut context, cache);

    // for binding in refinements.bindings {
    //     context.solver.assert(binding);
    // }

    // for assert in refinements.asserts {
    //     // We must push and pop asserts each time otherwise the
    //     // first unsat result will cause all following results to be unsat
    //     context.solver.push();
    //     context.solver.assert(context.z3_context.not(assert.0));
    //     match context.solver.check() {
    //         z3::SatResult::Sat(model) => {
    //             context.issue_refinement_error(assert.0, model, cache, assert.1, assert.2);
    //         },
    //         z3::SatResult::Unsat => {},
    //         z3::SatResult::Unknown(reason) => {
    //             error!(assert.1, "error while solving {}: {}", context.z3_context.ast_to_string(assert.0), reason);
    //         }
    //     }
    //     context.solver.pop();
    // }
}

pub trait Refineable<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement;
}

impl<'c> Refineable<'c> for ast::Ast<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        dispatch_on_expr!(self, Refineable::refine, context, cache)
    }
}

impl<'c> Refineable<'c> for ast::Literal<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        use crate::parser::ast::LiteralKind;
        match &self.kind {
            LiteralKind::Char(c) => Refinement::Integer(*c as i64),
            LiteralKind::Bool(b) => Refinement::Boolean(*b),
            LiteralKind::Float(f) => Refinement::Float(*f),
            LiteralKind::Integer(i, kind) => Refinement::Integer(*i as i64),
            LiteralKind::String(_) => Refinement::Integer(0), // TODO // context.string_value(s),
            LiteralKind::Unit => Refinement::Integer(0),
        }
    }
}

impl<'c> Refineable<'c> for ast::Variable<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        let definition_id = self.definition.unwrap();

        match context.lookup(definition_id) {
            Some(refinements) => refinements.clone(),
            None => context.refine_definition(definition_id, cache),
        }
    }
}

fn refine_lambda<'c>(lambda: &ast::Lambda<'c>, name: &str,
    context: &mut RefinementContext,
    cache: &ModuleCache<'c>) -> Refinement
{
    let parameters = fmap(&lambda.args, |parameter| {
        context.refine_pattern(parameter, cache)
    });

    let body = lambda.body.refine(context, cache);
}

impl<'c> Refineable<'c> for ast::Lambda<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        let name = format!("lambda@{:?}:{}:{}", self.location.filename, self.location.start.line, self.location.start.column);
        refine_lambda(self, &name, context, cache)
    }
}

impl<'c> Refineable<'c> for ast::FunctionCall<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        let f = self.function.refine(context, cache);
        let args = fmap(&self.args, |arg| arg.refine(context, cache));

        match f.extract_function() {
            Some((params, ret, mut statements)) => {
                let mut replacements = vec![];

                for (param, arg) in params.into_iter().zip(statements) {
                    let (rs, ss) = param.match_pattern(arg, self.location);
                    replacements.append(&mut rs);
                    statements.append(&mut ss);
                }

                let ret = ret.substitute(&replacements, self.location);
                if statements.is_empty() {
                    ret
                } else {
                    statements.push(ret);
                    Refinement::Block(statements)
                }
            },
            _ => {
                error!(self.location, "Found a non-function thingy here")
            }
        }
    }
}

impl<'c> Refineable<'c> for ast::Definition<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
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

impl<'c> Refineable<'c> for ast::If<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        let cond = self.condition.refine(context, cache);
        let then = self.then.refine(context, cache);

        let (mut asserts, mut bindings) = cond.implies(then, context.z3_context);

        if let Some(otherwise) = self.otherwise.as_ref() {
            let otherwise = otherwise.refine(context, cache);

            let not = cond.map_value(|cond| context.z3_context.not(cond));
            let mut otherwise = not.implies(otherwise, context.z3_context);

            asserts.append(&mut otherwise.0);
            bindings.append(&mut otherwise.1);
        }

        let value = context.unrepresentable_value(self.typ.as_ref().unwrap(), cache);
        Refinement::new(value, asserts, bindings)
    }
}

impl<'c> Refineable<'c> for ast::Match<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        let match_expr = self.expression.refine(context, cache);

        let cases = fmap(&self.branches, |(pattern, branch)| {
            (pattern.refine(context, cache), branch.refine(context, cache))
        });

        Refinement::Case(match_expr, cases)
    }
}

impl<'c> Refineable<'c> for ast::TypeDefinition<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::TypeAnnotation<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        self.lhs.refine(context, cache)
    }
}

impl<'c> Refineable<'c> for ast::Import<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::TraitDefinition<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::TraitImpl<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        for definition in self.definitions.iter() {
            // TODO: verify any assertions, check that nothing should bubble up
            definition.refine(context, cache);
        }

        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::Return<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        // TODO: Handle early returns
        self.expression.refine(context, cache)
    }
}

impl<'c> Refineable<'c> for ast::Sequence<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        Refinement::combine_all(
            self.statements.iter()
                .map(|statement| statement.refine(context, cache))
        )
    }
}

impl<'c> Refineable<'c> for ast::Extern<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::MemberAccess<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        // TODO lookup datatype accessor
        context.unrepresentable(self.typ.as_ref().unwrap(), cache)
    }
}

impl<'c> Refineable<'c> for ast::Assignment<'c> {
    fn refine(&self, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        // TODO, either phi value or taint lhs
        self.rhs.refine(context, cache)
    }
}
