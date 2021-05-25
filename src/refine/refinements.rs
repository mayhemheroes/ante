use crate::refine::context::{ Z3Ast, Z3Bool };
use crate::util::{ fmap, join_with };
use crate::error::location::Location;
use std::rc::Rc;
use z3::ast::Ast;

/// Each assert is a boolean z3 expression along with (in order)
/// the callsite it was instantiated at and the origin of the
/// refinement. The later is usually the function or type definition
/// where the refinement was declared.
type Asserts<'z3, 'c> = Vec<(Z3Bool<'z3>, Location<'c>, Location<'c>)>;

type Bindings<'z3> = Vec<Z3Bool<'z3>>;

#[derive(Clone)]
pub struct Refinements<'z3, 'c> {
    pub value: RefinementValue<'z3>,
    pub asserts: Asserts<'z3, 'c>,
    pub bindings: Bindings<'z3>,
}

impl<'z3, 'c> Refinements<'z3, 'c> {
    pub fn unit(context: &'z3 z3::Context) -> Self {
        Refinements::from_value(Self::unit_value(context))
    }

    pub fn from_value(value: Z3Ast<'z3>) -> Self {
        Refinements {
            value: RefinementValue::Pure(value),
            asserts: vec![],
            bindings: vec![],
        }
    }

    pub fn new(value: RefinementValue<'z3>, asserts: Asserts<'z3, 'c>, bindings: Bindings<'z3>) -> Self {
        Refinements { value, asserts, bindings }
    }

    pub fn function(value: z3::FuncDecl<'z3>, params: Vec<Z3Ast<'z3>>) -> Self {
        Refinements {
            value: RefinementValue::Function(Rc::new((value, params))),
            asserts: vec![],
            bindings: vec![],
        }
    }

    pub fn impure() -> Self {
        Self::new(RefinementValue::Impure, vec![], vec![])
    }

    fn unit_value(context: &'z3 z3::Context) -> z3::ast::Dynamic<'z3> {
        z3::ast::Bool::fresh_const(context, "unit").into()
    }

    pub fn combine(self, other: Self) -> Self {
        self.combine_with(other, |this, _| this)
    }

    pub fn combine_all(mut refinements: impl Iterator<Item = Self>) -> Self {
        let mut result = refinements.next().unwrap();

        for refinement in refinements {
            result = result.combine(refinement);
        }

        result
    }

    /// Combine the two Refinements, appending the assertions
    /// and bindings from each then applying the given function
    /// to the result and the value of the other RefinementValue.
    pub fn combine_with<F>(mut self, mut other: Self, f: F) -> Self
        where F: FnOnce(Self, RefinementValue<'z3>) -> Self
    {
        self.asserts.append(&mut other.asserts);
        self.bindings.append(&mut other.bindings);

        if other.value.is_impure() {
            self.value = RefinementValue::Impure;
        }

        f(self, other.value)
    }

    pub fn get_func_decl(&self) -> Option<&(z3::FuncDecl<'z3>, Vec<Z3Ast<'z3>>)> {
        match &self.value {
            RefinementValue::Function(f) => Some(f.as_ref()),
            _ => None,
        }
    }

    pub fn get_value(&self) -> Option<Z3Ast<'z3>> {
        match &self.value {
            RefinementValue::Pure(x) => Some(x.clone()),
            _ => None,
        }
    }

    pub fn set_return(mut self, ret: Z3Ast<'z3>) -> Self {
        self.value = RefinementValue::Pure(ret);
        self
    }

    pub fn map<F>(self, f: F) -> Self
        where F: FnOnce(Z3Ast<'z3>, Asserts<'z3, 'c>) -> Self
    {
        match self.value {
            RefinementValue::Pure(value) => f(value, self.asserts),
            _ => self,
        }
    }

    pub fn map_value<F>(mut self, f: F) -> Self
        where F: FnOnce(Z3Ast<'z3>) -> Z3Ast<'z3>
    {
        if let RefinementValue::Pure(value) = self.value {
            self.value = RefinementValue::Pure(f(value));
        }
        self
    }

    pub fn bind_to(self, other: Self) -> Self {
        self.combine_with(other, |mut this, other_value| {
            if let RefinementValue::Pure(value) = this.value {
                if let RefinementValue::Pure(other_value) = &other_value {
                    let eq = value._eq(other_value);
                    this.bindings.push(eq);
                }
            }

            this.value = other_value;
            this
        })
    }

    /// Map all the asserts in other, returning a new Vec of
    /// asserts in the form (=> self.value other.assert)
    pub fn implies(&self, other: Self) -> (Asserts<'z3, 'c>, Bindings<'z3>) {
        match &self.value {
            RefinementValue::Pure(value) => {
                let cond = value.as_bool().unwrap();
                let asserts = fmap(&other.asserts, |assert| (cond.implies(&assert.0), assert.1, assert.2));
                (asserts, other.bindings)
            },
            _ => {
                println!("Self value isn't pure, its: {}", self);
                (other.asserts, other.bindings)
            },
        }
    }

    pub fn try_add_assert(mut self, assert: Option<Self>, location: Location<'c>) -> Self {
        if let Some(assert) = assert {
            let assert_value = assert.get_value().unwrap();
            let assert_value = assert_value.as_bool().unwrap();
            self.asserts.push((assert_value, location, location));
        }
        self
    }

    pub fn substitute(mut self, replacements: Vec<(&Z3Ast<'z3>, Self)>, callsite: Location<'c>) -> Self {
        let mut all_asserts = vec![];
        let mut all_bindings = vec![];
        let mut substitutions = vec![];

        for (pattern, mut refinement) in replacements {
            all_asserts.append(&mut refinement.asserts);
            all_bindings.append(&mut refinement.bindings);

            match refinement.value {
                RefinementValue::Pure(value) => substitutions.push((pattern, value)),
                _ => (),
            }
        }

        let substitutions: Vec<_> = substitutions.iter().map(|sub| (sub.0, &sub.1)).collect();
        self.value = self.value.substitute(&substitutions);
        self.asserts = fmap(&self.asserts, |assert| (assert.0.substitute(&substitutions), callsite, assert.2));
        self.bindings = fmap(&self.bindings, |binding| binding.substitute(&substitutions));

        self.asserts.append(&mut all_asserts);
        self.bindings.append(&mut all_bindings);
        self
    }
}

impl<'z3, 'c> std::fmt::Display for Refinements<'z3, 'c> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Value: {}", self.value)?;
        let asserts = self.asserts.iter().map(|assert| &assert.0).collect::<Vec<_>>();

        if self.asserts.len() == 1 {
            let asserts = join_with(&asserts, "\n");
            write!(f, "\nAsserts: {}", asserts)?;
        } else if asserts.len() > 1 {
            let asserts = join_with(&asserts, "\n");
            write!(f, "\nAsserts:\n{}", asserts)?;
        }

        if self.bindings.len() == 1 {
            let bindings = join_with(&self.bindings, "\n");
            write!(f, "\nBindings: {}", bindings)?;
        } else if self.bindings.len() > 1 {
            let bindings = join_with(&self.bindings, "\n");
            write!(f, "\nBindings:\n{}", bindings)?;
        }

        Ok(())
    }
}

#[derive(Clone)]
pub enum RefinementValue<'z3> {
    Function(Rc<(z3::FuncDecl<'z3>, Vec<Z3Ast<'z3>>)>),
    Pure(Z3Ast<'z3>),
    Impure,
}

impl<'z3> RefinementValue<'z3> {
    pub fn is_impure(&self) -> bool {
        match self {
            RefinementValue::Impure => true,
            _ => false,
        }
    }

    pub fn substitute(self, replacements: &[(&Z3Ast<'z3>, &Z3Ast<'z3>)]) -> RefinementValue<'z3> {
        use RefinementValue::*;
        match self {
            Pure(ast) => Pure(ast.substitute(replacements)),
            Function(f) => {
                let args = fmap(&f.1, |arg| arg.substitute(replacements));
                let arg_refs: Vec<_> = args.iter().collect();
                Pure(f.0.apply(&arg_refs))
            },
            Impure => Impure,
        }
    }
}

impl<'z3> std::fmt::Display for RefinementValue<'z3> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RefinementValue::Pure(ast) => write!(f, "{}", ast),
            RefinementValue::Function(fd) => {
                let params = join_with(&fd.1, " ");
                write!(f, "fn {} -> {}", params, fd.0)
            },
            RefinementValue::Impure => write!(f, "Impure"),
        }
    }
}
