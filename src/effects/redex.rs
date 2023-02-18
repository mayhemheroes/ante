use crate::hir::FunctionCall;
use crate::hir::Lambda;
use crate::util::fmap;
use crate::hir::MemberAccess;
use crate::hir::DefinitionId;
use crate::hir::Ast;
use crate::hir::Tuple;

pub fn simplify(ast: Ast) -> Ast {
    match ast {
        Ast::Literal(_) => ast,
        Ast::Variable(_) => ast,
        Ast::Lambda(lambda) => {
            Ast::Lambda(Lambda {
                args: lambda.args,
                body: Box::new(simplify(*lambda.body)),
                typ: lambda.typ,
            })
        },
        Ast::FunctionCall(call) => match *call.function {
            Ast::Lambda(lambda) => {
                let substitutions = lambda.args.iter().map(|arg| arg.definition_id).zip(&call.args).collect::<Vec<_>>();
                simplify(substitute(*lambda.body, &substitutions))
            },
            function => {
                let function = Box::new(simplify(function));
                let args = fmap(call.args, simplify);
                Ast::FunctionCall(FunctionCall {
                    function,
                    args,
                    function_type: call.function_type,
                })
            },
        },
        Ast::Definition(_) => todo!(),
        Ast::If(_) => todo!(),
        Ast::Match(_) => todo!(),
        Ast::Return(_) => todo!(),
        Ast::Sequence(_) => todo!(),
        Ast::Extern(_) => ast,
        Ast::Assignment(_) => todo!(),
        Ast::MemberAccess(access) => {
            Ast::MemberAccess(MemberAccess {
                lhs: Box::new(simplify(*access.lhs)),
                member_index: access.member_index,
            })
        },
        Ast::Tuple(tuple) => Ast::Tuple(Tuple { fields: fmap(tuple.fields, simplify) }),
        Ast::ReinterpretCast(_) => todo!(),
        Ast::Builtin(_) => todo!(),
    }
}

fn substitute(ast: Ast, substitutions: &[(DefinitionId, &Ast)]) -> Ast {
    match ast {
        ast @ Ast::Literal(_) => ast,
        Ast::Variable(var) => {
            substitutions.iter()
                .find(|(key, _)| *key == var.definition_id)
                .map(|(_, new_value)| (*new_value).clone())
                .unwrap_or(Ast::Variable(var))
        }
        Ast::Lambda(lambda) => {
            Ast::Lambda(Lambda {
                args: lambda.args,
                body: Box::new(substitute(*lambda.body, substitutions)),
                typ: lambda.typ,
            })
        },
        Ast::FunctionCall(call) => {
            Ast::FunctionCall(FunctionCall {
                function: Box::new(substitute(*call.function, substitutions)),
                args: fmap(call.args, |arg| substitute(arg, substitutions)),
                function_type: call.function_type,
            })
        },
        Ast::Definition(_) => todo!(),
        Ast::If(_) => todo!(),
        Ast::Match(_) => todo!(),
        Ast::Return(_) => todo!(),
        Ast::Sequence(_) => todo!(),
        Ast::Extern(_) => todo!(),
        Ast::Assignment(_) => todo!(),
        Ast::MemberAccess(access) => {
            Ast::MemberAccess(MemberAccess {
                lhs: Box::new(substitute(*access.lhs, substitutions)),
                member_index: access.member_index,
            })
        },
        Ast::Tuple(tuple) => Ast::Tuple(Tuple { fields: fmap(tuple.fields, |field| substitute(field, substitutions)) }),
        Ast::ReinterpretCast(_) => todo!(),
        Ast::Builtin(_) => todo!(),
    }
}
