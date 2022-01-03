use crate::error::location::Locatable;
use crate::parser::ast;
use crate::cache::ModuleCache;
use crate::refinements::context::RefinementContext;
use crate::refinements::types::{Refinement, RefinementType};
use crate::types::typed::Typed;

mod context;
mod z3;
mod model_parser;
pub mod types;

pub fn refine<'c>(ast: &ast::Ast<'c>, output_refinements: bool, cache: &mut ModuleCache<'c>) {
    let mut context = RefinementContext::new();
    let refinement = check(ast, &RefinementType::unit(cache), &mut context, cache);

    if output_refinements {
        println!("{}", refinement);
    }

    // TODO: currently some extra refinements are being created (possibly from
    //       RefinementContext::named) that causes the solver to fail
    //
    // let z3_context = z3::Context::new();
    // let condition = z3_context.convert_refinement(&refinement, cache);
    // let solver = z3::Solver::new(z3_context);
    // solver.assert(z3_context.not(condition));

    // match solver.check() {
    //     z3::SatResult::Sat(model) => {
    //         model_parser::issue_refinement_error(z3_context, condition, model, cache, ast.locate(), ast.locate());
    //     },
    //     z3::SatResult::Unsat => println!("Could not prove condition"),
    //     z3::SatResult::Unknown(reason) => println!("Unknown error: {}", reason),
    // }
}

fn check<'c>(ast: &ast::Ast<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    use ast::Ast::*;
    match ast {
        Lambda(lambda) => check_lambda(lambda, typ, context, cache),
        Definition(definition) => check_definition(definition, context, cache),
        If(if_expr) => check_if(if_expr, typ, context, cache),
        Match(match_expr) => check_match(match_expr, typ, context, cache),
        Return(return_expr) => check_return(return_expr, typ, context, cache),
        Sequence(sequence) => check_sequence(sequence, typ, context, cache),
        other => check_synthesize(other, typ, context, cache),
    }
}

fn synthesize<'c>(ast: &ast::Ast<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    use ast::Ast::*;
    match ast {
        Literal(literal) => synthesize_literal(literal, context, cache),
        Variable(variable) => synthesize_variable(variable, context, cache),
        FunctionCall(call) => synthesize_call(call, context, cache),
        TypeAnnotation(annotation) => synthesize_type_annotation(annotation, context, cache),
        Return(return_expr) => synthesize_return(return_expr, context, cache),
        Sequence(sequence) => synthesize_sequence(sequence, context, cache),
        other => {
            // Default synthesize that does nothing for constructs like type definitions
            // where nothing needs to be done (at least currently in ante)
            (Refinement::true_(), context.convert_type(other.get_type().unwrap(), cache))
        }
    }
}

// [Chk-Syn]
// G |- e ==> s        G |- s <: t
// ----------------------------------
//           G |- e <== t
fn check_synthesize<'c>(ast: &ast::Ast<'c>, t: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (r1, s) = synthesize(ast, context, cache);
    let r2 = s.check_subtype(t, context, cache);

    r1.and(r2)
}

fn synthesize_literal<'c>(ast: &ast::Literal<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    let typ = ast.get_type().unwrap();
    let (base, id, r) = context.convert_type(typ, cache).unwrap_base();

    let value = match &ast.kind {
        ast::LiteralKind::Integer(x, _) => Some(Refinement::Integer(*x as i64)),
        ast::LiteralKind::Float(f) => Some(Refinement::Float(*f)),
        ast::LiteralKind::String(_) => None,
        ast::LiteralKind::Char(c) => Some(Refinement::Integer(*c as i64)),
        ast::LiteralKind::Bool(b) => Some(Refinement::Boolean(*b)),
        ast::LiteralKind::Unit => Some(Refinement::Unit),
    };

    // Add the constraint this == value for the literal's refined type
    let refinement = match value {
        Some(value) => r.and(Refinement::Variable(id).eq(value)),
        None => r,
    };
    let typ = RefinementType::Base(base, id, refinement);
    (Refinement::true_(), typ)
}

// [Syn-Var] 
// ----------------- 
//  G |- x ==> G(x)
fn synthesize_variable<'c>(ast: &ast::Variable<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    (Refinement::true_(), context.lookup_or_create(ast.definition.unwrap(), cache))
}

// [Chk-Lam] 
//  G, x:s[y:=x] |- e <== t[y:=x]
//  -----------------------------
//  G |- \x.e <== y:s -> t
fn check_lambda<'c>(ast: &ast::Lambda<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (ys, mut t) = typ.clone().unwrap_function();

    for (x, (y, s)) in ast.args.iter().zip(ys.iter()) {
        let (_, x, x_id) = RefinementContext::named(x, cache);
        context.insert_refinement(x_id, s.substitute(*y, &x));
        t = t.substitute(*y, &x);
    }

    let r = check(ast.body.as_ref(), &t, context, cache);

    // Must remove parameters from context afterward
    for (y, _) in ys {
        context.remove_refinement(y);
    }

    r
}

// [Syn-App]
// G |- e ==> x:s -> t
// G |- y <== s
// -----------------------
// G |- e y ==> t[x := y]
fn synthesize_call<'c>(ast: &ast::FunctionCall<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    let (mut r, f) = synthesize(ast.function.as_ref(), context, cache);
    let (xs, mut t) = f.unwrap_function();

    for (y, (x, s)) in ast.args.iter().zip(xs) {
        let (y_ast, y, _) = RefinementContext::named(y, cache);
        r = r.and(check(&y_ast, &s, context, cache));
        t = t.substitute(x, &y);
    }
    (r, t)
}

fn check_definition<'c>(ast: &ast::Definition<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    match ast.expr.as_ref() {
        ast::Ast::Lambda(_) => check_definition_recursive(ast, context, cache),
        _ => check_definition_nonrecursive(ast, context, cache),
    }
}

// [Chk-Let] 
// G |- e ==> s        G, x:s |- e' <== t'
// -------------------------------------------
//     G |- let x = e in e' <== t'
fn check_definition_nonrecursive<'c>(ast: &ast::Definition<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (r, s) = synthesize(ast.expr.as_ref(), context, cache);
    // context.bind_pattern(ast.pattern.as_ref(), s);
    let r = r.and(check(ast.pattern.as_ref(), &s, context, cache));

    // TODO: expand/generalize
    if let ast::Ast::Variable(x) = ast.pattern.as_ref() {
        context.insert_refinement(x.definition.unwrap(), s.clone());
    }

    r
}

// [Chk-Rec] 
// t := fresh(s)    G; f:t |- e <== t    G; f:t |- e' <== t'
// ---------------------------------------------------------
// G |- letrec f = (e:s) in e' <== t'
fn check_definition_recursive<'c>(ast: &ast::Definition<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let t = context.convert_type(ast.expr.get_type().unwrap(), cache);

    // TODO: expand - though this should be the only valid pattern for a function rhs anyway
    if let ast::Ast::Variable(f) = ast.pattern.as_ref() {
        context.insert_refinement(f.definition.unwrap(), t.clone());
    }

    check(ast.expr.as_ref(), &t, context, cache)
}

// [Chk-If]
// G            |- v  <== bool    
// G, _:{v}     |- e1 <== typ     
// G, _:{not v} |- e2 <== typ
// -----------------------------
// G |- if v e1 e2 <== typ
fn check_if<'c>(ast: &ast::If<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (v_ast, v, v_id) = RefinementContext::named(ast.condition.as_ref(), cache);

    let mut r = check(&v_ast, &RefinementType::bool(cache), context, cache);
    let rt = r.clone().and(v.clone());
    let rf = r.clone().and(v.not());

    let t = RefinementType::bool_refined(rt, cache);
    context.insert_refinement(v_id, t);
    r = r.and(check(ast.then.as_ref(), typ, context, cache));
    context.remove_refinement(v_id);

    if let Some(otherwise) = ast.otherwise.as_ref() {
        let t = RefinementType::bool_refined(rf, cache);
        context.insert_refinement(v_id, t);
        r = r.and(check(otherwise.as_ref(), typ, context, cache));
        context.remove_refinement(v_id);
    }

    r
}

// [Chk-Switch]
// G | y |- a_i <== t  for each i
// ---------------------------
// G |- switch y {a_1...} <== t
fn check_match<'c>(ast: &ast::Match<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let y = ast.expression.as_ref();
    let mut r = Refinement::true_();
    for (pattern, branch) in ast.branches.iter() {
        r = r.and(check_alt(y, pattern, branch, typ, context, cache));
    }
    r
}

// [Chk-Alt]
// s = ctor(G, D, y)    G' = unapply(G, y, zs, s)   G' |- e <== t
// --------------------------------------------------------------- 
// G | y |- C z... -> e <== t
fn check_alt<'c>(y: &ast::Ast<'c>, pattern: &ast::Ast<'c>, e: &ast::Ast<'c>, t: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    // let s = ctor(context, pattern, y);
    // unapply(context, y, zs, s);
    let r = check(e, t, context, cache);
    // reapply(context, y, zs, s);
    r
}

// [Syn-Ann]
// G |- e <== t   t := fresh(s)
// ---------------------------
// G |- e:s ==> t
fn synthesize_type_annotation<'c>(ast: &ast::TypeAnnotation<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    let t = context.convert_type(ast.typ.as_ref().unwrap(), cache);
    let r = check(ast.lhs.as_ref(), &t, context, cache);
    (r, t)
}

fn check_return<'c>(ast: &ast::Return<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    check(ast.expression.as_ref(), typ, context, cache)
}

fn synthesize_return<'c>(ast: &ast::Return<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    synthesize(ast.expression.as_ref(), context, cache)
}

fn check_sequence<'c>(ast: &ast::Sequence<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let mut r = Refinement::Boolean(true);

    let unit = RefinementType::unit(cache);
    for statement in ast.statements.iter().take(ast.statements.len() - 1) {
        r = r.and(check(statement, &unit, context, cache));
    }

    let last = ast.statements.last().unwrap();
    r.and(check(last, typ, context, cache))
}

fn synthesize_sequence<'c>(ast: &ast::Sequence<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    let mut r = Refinement::Boolean(true);

    let unit = RefinementType::unit(cache);
    for statement in ast.statements.iter().take(ast.statements.len() - 1) {
        r = r.and(check(statement, &unit, context, cache));
    }

    let last = ast.statements.last().unwrap();
    let (last_r, last_t) = synthesize(last, context, cache);
    (r.and(last_r), last_t)
}

/*
impl<'c> Refineable<'c> for ast::Extern<'c> {
    fn check(ast: &ast::, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
        todo!()
    }

    fn synthesize(&ast, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
        todo!()
    }
}

impl<'c> Refineable<'c> for ast::MemberAccess<'c> {
    fn check(ast: &ast::, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
        todo!()
    }

    fn synthesize(&ast, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
        todo!()
    }
}

impl<'c> Refineable<'c> for ast::Assignment<'c> {
    fn check(ast: &ast::, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
        todo!()
    }

    fn synthesize(&ast, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
        todo!()
    }
}
*/
