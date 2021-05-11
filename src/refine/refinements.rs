use crate::refine::context::{ Z3Ast, Z3Bool };
use crate::util::{ fmap, join_with };
use crate::error::location::Location;
use std::rc::Rc;
use z3::ast::Ast;

type Asserts<'z3, 'c> = Vec<(Z3Bool<'z3>, Location<'c>)>;

#[derive(Clone)]
pub enum Refinements<'z3, 'c> {
    Impure,
    Pure {
        value: RefinementValue<'z3>,
        asserts: Asserts<'z3, 'c>,
    },
}

impl<'z3, 'c> Refinements<'z3, 'c> {
    pub fn none() -> Self {
        Refinements::Pure {
            value: RefinementValue::Unrepresentable,
            asserts: vec![],
        }
    }

    pub fn new(value: Z3Ast<'z3>) -> Self {
        Refinements::Pure {
            value: RefinementValue::Pure(value),
            asserts: vec![],
        }
    }

    pub fn function(value: z3::FuncDecl<'z3>, params: Vec<Z3Ast<'z3>>) -> Self {
        Refinements::Pure {
            value: RefinementValue::Function(Rc::new((value, params))),
            asserts: vec![],
        }
    }

    pub fn with_asserts(asserts: Asserts<'z3, 'c>) -> Self {
        Refinements::Pure {
            value: RefinementValue::Unrepresentable,
            asserts,
        }
    }

    pub fn combine(self, other: Self) -> Self {
        match other {
            Refinements::Pure { asserts, .. } => {
                self.add_asserts(asserts)
            },
            Refinements::Impure => Refinements::Impure,
        }
    }

    pub fn add_asserts(self, mut more_asserts: Asserts<'z3, 'c>) -> Self {
        match self {
            Refinements::Pure { value, mut asserts } => {
                asserts.append(&mut more_asserts);
                Refinements::Pure { value, asserts }
            },
            Refinements::Impure => Refinements::Impure,
        }
    }

    pub fn get_func_decl(&self) -> Option<&(z3::FuncDecl<'z3>, Vec<Z3Ast<'z3>>)> {
        match self {
            Refinements::Pure { value: RefinementValue::Function(f), .. } => Some(f.as_ref()),
            _ => None,
        }
    }

    pub fn get_value(&self) -> Option<Z3Ast<'z3>> {
        match self {
            Refinements::Pure { value: RefinementValue::Pure(x), .. } => Some(x.clone()),
            _ => None,
        }
    }

    pub fn set_return(self, ret: Z3Ast<'z3>) -> Self {
        match self {
            Refinements::Impure => Refinements::Impure,
            Refinements::Pure { asserts, .. } => {
                let value = RefinementValue::Pure(ret);
                Refinements::Pure { value, asserts }
            }
        }
    }

    pub fn set_unrepresentable(self) -> Self {
        match self {
            Refinements::Impure => Refinements::Impure,
            Refinements::Pure { asserts, .. } => {
                let value = RefinementValue::Unrepresentable;
                Refinements::Pure { value, asserts }
            }
        }
    }

    pub fn map<F>(self, f: F) -> Self
        where F: FnOnce(Z3Ast<'z3>, Asserts<'z3, 'c>) -> Self
    {
        match self {
            Refinements::Pure { value: RefinementValue::Pure(value), asserts } => {
                f(value, asserts)
            },
            other => other,
        }
    }

    pub fn map_value<F>(self, f: F) -> Self
        where F: FnOnce(Z3Ast<'z3>) -> Z3Ast<'z3>
    {
        match self {
            Refinements::Pure { value: RefinementValue::Pure(value), asserts } => {
                Refinements::Pure { value: RefinementValue::Pure(f(value)), asserts }
            },
            other => other,
        }
    }

    pub fn bind_to(self, solver: &z3::Solver<'z3>, other: Self) -> Self {
        self.map(|value, mut asserts| {
            match other {
                Refinements::Pure { value: RefinementValue::Pure(other_value), asserts: mut other_asserts } => {
                    let eq = value._eq(&other_value);
                    solver.assert(&eq);
                    asserts.append(&mut other_asserts);
                    Refinements::Pure { value: RefinementValue::Pure(value), asserts }
                },
                Refinements::Pure { value: RefinementValue::Function(f), asserts: mut other_asserts } => {
                    asserts.append(&mut other_asserts);
                    Refinements::Pure { value: RefinementValue::Function(f), asserts }
                },
                other => other,
            }
        })
    }

    /// Create new Refinements from `other` with each boolean
    /// clause b replaced with (self.value => b)
    pub fn implies(self, other: Self) -> Self {
        other.map(|_, asserts| {
            self.map(|self_value, mut self_asserts| {
                let cond = self_value.as_bool().unwrap();
                let mut asserts = fmap(&asserts, |assert| (cond.implies(&assert.0), assert.1));
                asserts.append(&mut self_asserts);
                let value = RefinementValue::Unrepresentable;
                Refinements::Pure { value, asserts }
            })
        })
    }

    pub fn try_add_assert(self, assert: Option<Self>, location: Location<'c>) -> Self {
        if let Some(assert) = assert {
            match self {
                Refinements::Pure { value, mut asserts } => {
                    let assert_value = assert.get_value().unwrap();
                    asserts.push((assert_value.as_bool().unwrap(), location));
                    Refinements::Pure { value, asserts }
                },
                Refinements::Impure => Refinements::Impure,
            }
        } else {
            self
        }
    }

    pub fn substitute(self, replacements: Vec<(&Z3Ast<'z3>, Self)>, callsite: Location<'c>) -> Self {
        let mut all_asserts = vec![];
        let mut substitutions = vec![];

        for (pattern, refinement) in replacements {
            match refinement {
                Refinements::Pure { value, mut asserts } => {
                    all_asserts.append(&mut asserts);

                    match value {
                        RefinementValue::Pure(value) => substitutions.push((pattern, value)),
                        RefinementValue::Function(_) => (),
                        RefinementValue::Unrepresentable => (),
                    }
                },
                Refinements::Impure => (),
            }
        }

        let substitutions: Vec<_> = substitutions.iter().map(|sub| (sub.0, &sub.1)).collect();
        match self {
            Refinements::Pure { value, asserts } => {
                Refinements::Pure {
                    value: value.substitute(&substitutions),
                    asserts: fmap(&asserts, |assert| (assert.0.substitute(&substitutions), callsite)),
                }
            },
            Refinements::Impure => Refinements::Impure,
        }
    }
}

impl<'z3, 'c> std::fmt::Display for Refinements<'z3, 'c> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Refinements::Pure { value, asserts } => {
                write!(f, "Value: {}", value)?;
                let asserts = asserts.iter().map(|assert| &assert.0).collect::<Vec<_>>();

                if asserts.len() == 1 {
                    let asserts = join_with(&asserts, "\n");
                    write!(f, "\nAsserts: {}", asserts)?;
                } else if asserts.len() > 1 {
                    let asserts = join_with(&asserts, "\n");
                    write!(f, "\nAsserts:\n{}", asserts)?;
                }

                Ok(())
            },
            Refinements::Impure => {
                write!(f, "Impure")
            }
        }
    }
}

#[derive(Clone)]
pub enum RefinementValue<'z3> {
    /// A value type (like char or unit) unrepresentable in z3
    Unrepresentable,
    Function(Rc<(z3::FuncDecl<'z3>, Vec<Z3Ast<'z3>>)>),
    Pure(Z3Ast<'z3>),
}

impl<'z3> RefinementValue<'z3> {
    pub fn substitute(self, replacements: &[(&Z3Ast<'z3>, &Z3Ast<'z3>)]) -> RefinementValue<'z3> {
        use RefinementValue::*;
        match self {
            Unrepresentable => Unrepresentable,
            Pure(ast) => Pure(ast.substitute(replacements)),
            Function(f) => {
                let args = fmap(&f.1, |arg| arg.substitute(replacements));
                let arg_refs: Vec<_> = args.iter().collect();
                Pure(f.0.apply(&arg_refs))
            },
        }
    }
}

impl<'z3> std::fmt::Display for RefinementValue<'z3> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RefinementValue::Unrepresentable => write!(f, "Unrepresentable"),
            RefinementValue::Pure(ast) => write!(f, "{}", ast),
            RefinementValue::Function(fd) => {
                let params = join_with(&fd.1, " ");
                write!(f, "fn {} -> {}", params, fd.0)
            },
        }
    }
}
