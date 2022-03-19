use crate::cache::ModuleCache;
use crate::util::fmap;
use crate::{cache::DefinitionInfoId, lifetimes};
use crate::lexer::token::Token;
use crate::types::{PrimitiveType, Type, TypeBinding, TypeInfoId, TypeVariableId};
use crate::refinements::context::RefinementContext;
use crate::util::reinterpret_from_bits;

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
    Forall(DefinitionInfoId, Box<RefinementType>, Box<Refinement>),
}

/// A RefinementType is a Type and a Refinement, t & r
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum RefinementType {
    // v:Base&r
    Base(BaseType, DefinitionInfoId, Refinement),

    // x:T -> ... -> U
    Function(Vec<NamedType>, Box<RefinementType>),
    TypeApplication(Box<RefinementType>, Vec<NamedType>),
    ForAll(Vec<TypeVariableId>, Box<RefinementType>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum BaseType {
    TypeVariable(TypeVariableId),
    Primitive(PrimitiveType),
    UserDefinedType(TypeInfoId),
    Ref(lifetimes::LifetimeVariableId),
}

pub type NamedType = (DefinitionInfoId, RefinementType);

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
            Variable(id) => vec![*id],
            Integer(_) => vec![],
            Boolean(_) => vec![],
            Float(_) => vec![],
            Unit => vec![],
            PrimitiveCall(_, args) => args.iter().flat_map(|arg| arg.find_variables()).collect(),
            Constructor(f, args)
            | Uninterpreted(f, args) => {
                let mut vars = vec![*f];
                for arg in args {
                    vars.append(&mut arg.find_variables());
                }
                vars
            }
            Forall(x, _t, e) => {
                let mut vars = vec![*x];
                vars.append(&mut e.find_variables());
                vars
            }
        }
    }

    pub fn substitute(&self, id: DefinitionInfoId, other: &Refinement) -> Refinement {
        use Refinement::*;
        match self {
            Variable(variable_id) if *variable_id == id => other.clone(),
            Variable(nonmatching_id) => Variable(*nonmatching_id),
            Integer(x) => Integer(*x),
            Boolean(b) => Boolean(*b),
            Float(f) => Float(*f),
            Unit => Unit,
            Constructor(f, args) => Constructor(*f, fmap(args, |arg| arg.substitute(id, other))),
            PrimitiveCall(f, args) => PrimitiveCall(*f, fmap(args, |arg| arg.substitute(id, other))),
            Uninterpreted(f, args) => Uninterpreted(*f, fmap(args, |arg| arg.substitute(id, other))),
            Forall(x, t, e) => Forall(*x, t.clone(), Box::new(e.substitute(id, other))),
        }
    }

    pub fn substitute_var(&self, id: DefinitionInfoId, replacement: DefinitionInfoId) -> Refinement {
        self.substitute(id, &Refinement::Variable(replacement))
    }

    pub fn true_() -> Refinement {
        Refinement::Boolean(true)
    }

    pub fn implies(self, other: Refinement) -> Refinement {
        match (self, other) {
            (Refinement::Boolean(true), other) => other,
            (_, Refinement::Boolean(true)) => Refinement::Boolean(true),
            (first, second) => Refinement::PrimitiveCall(Primitive::Implies, vec![first, second]),
        }
    }

    pub fn and(self, other: Refinement) -> Refinement {
        match (self, other) {
            (Refinement::Boolean(true), other) => other,
            (first, Refinement::Boolean(true)) => first,
            (first, second) => Refinement::PrimitiveCall(Primitive::And, vec![first, second]),
        }
    }

    pub fn eq(self, other: Refinement) -> Refinement {
        Refinement::PrimitiveCall(Primitive::Eq, vec![self, other])
    }

    pub fn not(self) -> Refinement {
        Refinement::PrimitiveCall(Primitive::Not, vec![self])
    }
}

impl std::fmt::Display for Refinement {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        use Refinement::*;
        match self {
            Variable(v) => write!(f, "v{}", v.0),
            Integer(x) => write!(f, "{}", *x),
            Boolean(b) => write!(f, "{}", *b),
            Float(x) => write!(f, "{}", reinterpret_from_bits(*x)),
            Unit => write!(f, "()"),
            PrimitiveCall(c, args) => {
                write!(f, "({}", c)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                write!(f, ")")
            }
            Uninterpreted(c, args)
            | Constructor(c, args) => {
                if !args.is_empty() {
                    write!(f, "(")?;
                }
                write!(f, "({}", c.0)?;
                for arg in args {
                    write!(f, " {}", arg)?;
                }
                if !args.is_empty() {
                    write!(f, ")")?;
                }
                Ok(())
            }
            Forall(x, t, e) => write!(f, "forall {}:{:?}. {}", x.0, *t, e),
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

impl RefinementType {
    /// Substitutes any free variables of matching id in the type
    /// with the given replacement.
    pub fn substitute(&self, id: DefinitionInfoId, replacement: &Refinement) -> RefinementType {
        use RefinementType::*;
        match self {
            Base(b, value_id, refinement) => {
                // Only substitute free variables
                let r = if *value_id == id {
                    refinement.clone()
                } else {
                    refinement.substitute(id, &replacement)
                };
                Base(*b, *value_id, r)
            },
            Function(args, ret) => {
                let mut found = false;
                let args = fmap(args, |(arg_id, arg)| {
                    if *arg_id == id || found {
                        found = found || *arg_id == id;
                        (*arg_id, arg.clone())
                    } else {
                        (*arg_id, arg.substitute(id, &replacement))
                    }
                });
                let ret = if found { ret.clone() } else { Box::new(ret.substitute(id, &replacement)) };
                Function(args, ret)
            }
            TypeApplication(constructor, args) => {
                let constructor = constructor.substitute(id, replacement);
                let mut found = false;
                let args = fmap(args, |(arg_id, arg)| {
                    if *arg_id == id || found {
                        found = found || *arg_id == id;
                        (*arg_id, arg.clone())
                    } else {
                        (*arg_id, arg.substitute(id, &replacement))
                    }
                });
                TypeApplication(Box::new(constructor), args)
            }
            ForAll(vars, typ) => ForAll(vars.clone(), Box::new(typ.substitute(id, replacement))),
        }
    }

    pub fn substitute_var(&self, id: DefinitionInfoId, replacement: DefinitionInfoId) -> RefinementType {
        self.substitute(id, &Refinement::Variable(replacement))
    }

    /// Return a tuple of (args, ret) if this is a function type,
    /// or panic otherwise.
    pub fn unwrap_function(self) -> (Vec<NamedType>, RefinementType) {
        match self {
            RefinementType::Function(args, ret) => (args, *ret),
            RefinementType::ForAll(_, typ) => typ.unwrap_function(),
            _ => unreachable!(),
        }
    }

    pub fn unwrap_base(self) -> (BaseType, DefinitionInfoId, Refinement) {
        match self {
            RefinementType::Base(b, id, r) => (b, id, r),
            _ => unreachable!(),
        }
    }

    // Is self a subtype of other?
    // Returns a set of constraints that would make this true
    pub fn check_subtype<'c>(&self, other: &RefinementType, context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
        match (self, other) {
            (RefinementType::Base(b1, id1, r1), RefinementType::Base(b2, id2, r2)) => check_subtype_base(*b1, *id1, r1, *b2, *id2, r2),
            (RefinementType::Function(args1, ret1), RefinementType::Function(args2, ret2)) =>
                check_subtype_fun(context, args1, ret1, args2, ret2, cache),
            (RefinementType::TypeApplication(c1, args1), RefinementType::TypeApplication(c2, args2)) =>
                check_subtype_tcon(c1, args1, c2, args2, context, cache),
            (a, b) => unreachable!("check_subtype found an uncaught type error while checking {:?} and {:?}", a, b),
        }
    }

    pub fn unit<'c>(cache: &mut ModuleCache<'c>) -> RefinementType {
        let id = cache.fresh_internal_var(Type::Primitive(PrimitiveType::UnitType));
        RefinementType::Base(BaseType::Primitive(PrimitiveType::UnitType), id, Refinement::true_())
    }

    pub fn bool<'c>(cache: &mut ModuleCache<'c>) -> RefinementType {
        let id = cache.fresh_internal_var(Type::Primitive(PrimitiveType::BooleanType));
        RefinementType::Base(BaseType::Primitive(PrimitiveType::BooleanType), id, Refinement::true_())
    }

    pub fn bool_refined<'c>(refinement: Refinement, cache: &mut ModuleCache<'c>) -> RefinementType {
        let id = cache.fresh_internal_var(Type::Primitive(PrimitiveType::BooleanType));
        RefinementType::Base(BaseType::Primitive(PrimitiveType::BooleanType), id, refinement)
    }

    pub fn dump<'c>(&self, cache: &ModuleCache<'c>) {
        match self {
            RefinementType::Base(b, id, r) => {
                print!("({}:", id.0);
                match b {
                    BaseType::TypeVariable(var) => {
                        // Sanity assert to ensure all bound typevars are already gone via convert_type
                        assert!(!matches!(&cache.type_bindings[var.0], TypeBinding::Bound(_)));
                        print!("tv{}", var.0);
                    },
                    BaseType::Primitive(primitive) => primitive.dump(cache),
                    BaseType::UserDefinedType(typ) => print!("{}", &cache.type_infos[typ.0].name),
                    BaseType::Ref(_lifetime) => print!("ref"),
                }
                print!(" & {})", r);
            },
            RefinementType::Function(args, ret) => {
                print!("(");
                for (id, arg) in args {
                    print!("{}:", id.0);
                    arg.dump(cache);
                    print!(" -> ");
                }
                ret.dump(cache);
                print!(")");
            },
            RefinementType::TypeApplication(f, args) => {
                print!("(");
                f.dump(cache);
                for (id, arg) in args {
                    print!(" {}:", id.0);
                    arg.dump(cache);
                }
                print!(")");
            },
            RefinementType::ForAll(vars, typ) => {
                print!("(forall");
                for var in vars {
                    print!(" tv{}", var.0);
                }
                print!(". ");
                typ.dump(cache);
                print!(")");
            },
        }
    }
}

// [Ent-Ext]
// G |- forall x:b. p => c
// -----------------------
// G; x:b{x:p} |- c
//
// [Ent-Emp]
// SmtValid(c)
// -----------
// empty |- c
fn entails(context: &RefinementContext, c: &Refinement) -> Refinement {
    context.fold(c.clone(), |_id, p, c| {
        p.clone().implies(c)
    })
}

// [Sub-Base]  
//
// forall (v1:b). p1 => p2[v2 := v1]
// -------------------
// b{v1:p1} <: b{v2:p2}
fn check_subtype_base(_b1: BaseType, v1: DefinitionInfoId, p1: &Refinement, _b2: BaseType, v2: DefinitionInfoId, p2: &Refinement) -> Refinement {
    let q = p2.substitute_var(v2, v1);
    Refinement::implies(p1.clone(), q)
}

// [Sub-Fun]  
//
// s2 <: s1    x2:s2 |- t1[x1:=x2] <: t2 
// -------------------------------------
// x1:s1 -> t1 <: x2:s2 -> t2
fn check_subtype_fun<'c>(context: &mut RefinementContext, args1: &[NamedType],
    t1: &RefinementType, args2: &[NamedType], t2: &RefinementType, cache: &ModuleCache<'c>) -> Refinement
{
    let mut t1 = t1.clone();
    let mut r = Refinement::true_();

    for ((x1, s1), (x2, s2)) in args1.into_iter().zip(args2) {
        r = r.and(s2.check_subtype(s1, context, cache));
        context.insert_refinement(*x2, s2.clone());

        t1 = t1.substitute_var(*x1, *x2);
    }


    let r2 = t1.check_subtype(t2, context, cache);

    for ((x1, s1), (x2, s2)) in args1.into_iter().zip(args2) {
        context.remove_refinement(*x2);
    }

    r.and(r2)
}

// [Sub-TCon] 
//
// G,v:int{p} |- q[w:=v]     G |- si <: ti
// -----------------------------------------
// G |- (C s1...)[v|p] <: (C t1...)[w|q]
fn check_subtype_tcon<'c>(c1: &RefinementType, s1: &[NamedType], c2: &RefinementType, s2: &[NamedType], context: &mut RefinementContext, cache: &ModuleCache<'c>) -> Refinement {
    // TODO
    Refinement::true_()
}
