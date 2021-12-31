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
    let refinement = check(ast, &RefinementType::unit(), &mut context, cache);

    let z3_context = z3::Context::new();
    let condition = z3_context.convert_refinement(&refinement, cache);

    if output_refinements {
        println!("{}", refinement);
    }

    let solver = z3::Solver::new(z3_context);
    match solver.check() {
        z3::SatResult::Sat(model) => {
            println!("Could not prove condition");
        },
        z3::SatResult::Unsat => println!("Proved condition"),
        z3::SatResult::Unknown(reason) => println!("Unknown error: {}", reason),
    }

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

fn check<'c>(ast: &ast::Ast<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    use ast::Ast::*;
    match ast {
        Lambda(lambda) => check_lambda(lambda, typ, context, cache),
        Definition(definition) => check_definition(definition, typ, context, cache),
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
            println!("default synth on {}", ast);
            (Refinement::none(), context.convert_type(other.get_type().unwrap(), cache))
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
    use ast::LiteralKind::*;
    let typ = ast.get_type().unwrap();
    let this = cache.fresh_internal_var(typ.clone());

    let value = match &ast.kind {
        Integer(x, _) => Some(Refinement::Integer(*x as i64)),
        Float(f) => Some(Refinement::Float(*f)),
        String(_) => None,
        Char(c) => Some(Refinement::Integer(*c as i64)),
        Bool(b) => Some(Refinement::Boolean(*b)),
        Unit => Some(Refinement::Unit),
    };

    // Add the constraint this == value for the literal's refined type
    match context.convert_type(typ, cache) {
        RefinementType::Base(b, r) => {
            assert!(r.is_none());
            let refinement = value.map(|value| {
                let eq = Refinement::Variable(this).eq(value);
                (this, eq)
            });
            let typ = RefinementType::Base(b, refinement);
            (Refinement::none(), typ)
        },
        _ => unreachable!(),
    }
}

// [Syn-Var] 
// ----------------- 
//  G |- x ==> G(x)
fn synthesize_variable<'c>(ast: &ast::Variable<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    (Refinement::none(), context.lookup_or_create(ast.definition.unwrap(), cache))
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

// [Chk-Let] 
//  G |- e ==> s        G, x:s |- e' <== t'
//  -------------------------------------------
//      G |- let x = e in e' <== t'
//
fn check_definition<'c>(ast: &ast::Definition<'c>, _: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (r, s) = synthesize(ast.expr.as_ref(), context, cache);
    // context.bind_pattern(ast.pattern.as_ref(), s);
    let r = r.and(check(ast.pattern.as_ref(), &s, context, cache));
    r.and(check(ast.expr.as_ref(), &s, context, cache))
    // Ante's bindings have no `in e'`, the corresponding step is done in ast::Sequence::check
}

// [Chk-If]
// G            |- v  <== bool    
// G, _:{v}     |- e1 <== typ     
// G, _:{not v} |- e2 <== typ
// -----------------------------
// G |- if v e1 e2 <== typ
fn check_if<'c>(ast: &ast::If<'c>, typ: &RefinementType, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> Refinement {
    let (v_ast, v, v_id) = RefinementContext::named(ast.condition.as_ref(), cache);

    let mut r = check(&v_ast, &RefinementType::bool(), context, cache);
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
    let mut r = Refinement::none();
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

    let unit = RefinementType::unit();
    for statement in ast.statements.iter().take(ast.statements.len() - 1) {
        r = r.and(check(statement, &unit, context, cache));
    }

    let last = ast.statements.last().unwrap();
    r.and(check(last, typ, context, cache))
}

fn synthesize_sequence<'c>(ast: &ast::Sequence<'c>, context: &mut RefinementContext, cache: &mut ModuleCache<'c>) -> (Refinement, RefinementType) {
    let mut r = Refinement::Boolean(true);

    let unit = RefinementType::unit();
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
