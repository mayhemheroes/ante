use crate::{cache::DefinitionInfoId, lifetimes};
use crate::lexer::token::Token;

use super::{PrimitiveType, TypeInfoId, TypeVariableId};

/// These refinements are boolean expressions that can
/// narrow down the set of values a type accepts. Their
/// semantics are limited to a small logic usually solveable
/// by an SMT solver.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum Refinement {
    Variable(DefinitionInfoId),
    Integer(i64),
    Boolean(bool),
    Float(u64),
    Unit,
    Constructor(DefinitionInfoId, Vec<Refinement>),
    PrimitiveCall(Primitive, Vec<Refinement>),
    Uninterpreted(DefinitionInfoId, Vec<Refinement>),
}

/// A RefinementType is a Type and a Refinement, t & r
pub enum RefinementType {
    Base(BaseType, Option<Refinement>),
    Lambda(Vec<NamedType>, Box<RefinementType>),
    TypeApplication(BaseType, Vec<NamedType>),
    ForAll(Vec<TypeVariableId>, Box<RefinementType>),
}

pub enum BaseType {
    TypeVariable(TypeVariableId),
    Primitive(PrimitiveType),
    UserDefinedType(TypeInfoId),
    Ref(lifetimes::LifetimeVariableId),
}

pub struct NamedType(DefinitionInfoId, RefinementType);

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Primitive {
    Add, Sub, Mul, Div,
    Eq, Neq,
    Lt, Gt, Lte, Gte,
    Implies, And, Or, Not,
}

impl Refinement {
    pub fn find_variables(&self) -> Vec<DefinitionInfoId> {
        use Refinement::*;
        match self {
            Variable(v) => vec![*v],
            Integer(_) => vec![],
            Float(_) => vec![],
            Boolean(_) => vec![],
            Unit => vec![],
            PrimitiveCall(_, args) => {
                args.iter().flat_map(|arg| arg.find_variables()).collect()
            },
            Constructor(id, args)
            | Uninterpreted(id, args) => {
                let mut vars = vec![*id];
                let mut rest = args.iter().flat_map(|arg| arg.find_variables()).collect();
                vars.append(&mut rest);
                vars
            },
        }
    }
}

impl Primitive {
    pub fn from_token(token: &Token) -> Option<Primitive> {
        match token {
            Token::Add => Some(Primitive::Add),
            Token::Subtract => Some(Primitive::Sub),
            Token::Multiply => Some(Primitive::Mul),
            Token::Divide => Some(Primitive::Div),
            Token::EqualEqual => Some(Primitive::Eq),
            Token::NotEqual => Some(Primitive::Neq),
            Token::LessThan => Some(Primitive::Lt),
            Token::GreaterThan => Some(Primitive::Gt),
            Token::LessThanOrEqual => Some(Primitive::Lte),
            Token::GreaterThanOrEqual => Some(Primitive::Gte),
            Token::And => Some(Primitive::And),
            Token::Or => Some(Primitive::Or),
            Token::Not => Some(Primitive::Not),
            _ => None,
        }
    }
}

impl std::fmt::Display for Primitive {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Primitive::*;
        match self {
            Add => write!(f, "+"),
            Sub => write!(f, "-"),
            Mul => write!(f, "*"),
            Div => write!(f, "/"),
            Eq => write!(f, "=="),
            Neq => write!(f, "!="),
            Lt => write!(f, "<"),
            Gt => write!(f, ">"),
            Lte => write!(f, "<="),
            Gte => write!(f, ">="),
            Implies => write!(f, "=>"),
            And => write!(f, "and"),
            Or => write!(f, "or"),
            Not => write!(f, "not"),
        }
    }
}
