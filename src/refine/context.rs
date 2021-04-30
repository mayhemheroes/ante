use crate::cache::DefinitionInfoId;
use crate::util::fmap;
use std::collections::HashMap;
use z3::ast::{ Bool, Int, Float, String };

pub struct RefinementContext<'z3> {
    z3_context: &'z3 z3::Context,

    definitions: HashMap<DefinitionInfoId, Refinements<'z3>>,
}

pub struct DefinitionRefinementInfo<'z3> {
    refinements: Refinements<'z3>,
    parameters: Vec<DefinitionInfoId>,
}

type Z3Ast<'z3> = z3::ast::Dynamic<'z3>;
type Z3Bool<'z3> = z3::ast::Bool<'z3>;

pub struct Refinements<'z3> {
    value: Z3Ast<'z3>,
    bindings: Vec<Z3Bool<'z3>>,
    asserts: Vec<Z3Bool<'z3>>,
}

impl<'z3> RefinementContext<'z3> {
    pub fn new(z3_context: &'z3 z3::Context) -> RefinementContext<'z3> {
        RefinementContext { 
            z3_context,
            definitions: HashMap::new(),
        }
    }

    pub fn value<Ast: Into<Z3Ast<'z3>>>(ast: Ast) -> Option<Refinements<'z3>> {
        Some(Refinements::new(ast.into()))
    }

    pub fn bool_value(&self, value: bool) -> Option<Refinements<'z3>> {
        Self::value(Bool::from_bool(self.z3_context, value))
    }

    pub fn integer_value(&self, value: u64, signed: bool) -> Option<Refinements<'z3>> {
        let value = if signed {
            Int::from_i64(self.z3_context, value as i64)
        } else {
            Int::from_u64(self.z3_context, value)
        };
        Self::value(value)
    }

    pub fn float_value(&self, value: f64) -> Option<Refinements<'z3>> {
        Self::value(Float::from_f64(self.z3_context, value))
    }

    pub fn string_value(&self, value: &str) -> Option<Refinements<'z3>> {
        Self::value(String::from_str(self.z3_context, value).unwrap())
    }
}

impl<'z3> Refinements<'z3> {
    pub fn new(value: Z3Ast<'z3>) -> Refinements<'z3> {
        Refinements {
            value,
            bindings: vec![],
            asserts: vec![],
        }
    }
}

impl<'z3> DefinitionRefinementInfo<'z3> {
    pub fn new(refinements: Refinements<'z3>, parameters: &[DefinitionInfoId]) -> DefinitionRefinementInfo<'z3> {
        // let parameters = fmap(parameters, |param| param.0.to_string());
        DefinitionRefinementInfo {
            refinements,
            parameters: parameters.to_vec(),
        }
    }
}
