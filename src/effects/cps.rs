use crate::hir::FunctionType;
use crate::hir::PrimitiveType;
use crate::hir::DefinitionId;
use crate::hir::FunctionCall;
use crate::hir::DefinitionInfo;
use crate::hir::Ast;
use crate::hir::Lambda;
use crate::hir::Tuple;
use crate::hir::Type;
use crate::hir::Variable;
use crate::util::fmap;

pub fn convert_to_cps(ast: Ast) -> Ast {
    let mut context = Context::default();
    let initial_k = context.make_id_function();
    let cps_form = context.cps(&ast, initial_k);
    super::redex::simplify(cps_form)
}

#[derive(Default)]
struct Context {
    next_variable_id: usize,
}

fn make_call(f: Ast, args: Vec<Ast>) -> Ast {
    Ast::FunctionCall(FunctionCall {
        function: Box::new(f),
        args,
        function_type: todo_function_type(),
    })
}

fn todo_function_type() -> FunctionType {
    FunctionType {
        parameters: vec![Type::Primitive(PrimitiveType::Unit)],
        return_type: Box::new(Type::Primitive(PrimitiveType::Unit)),
        is_varargs: false,
    }
}

fn make_lambda(arg: Variable, body: Ast) -> Ast {
    Ast::Lambda(Lambda {
        args: vec![arg],
        body: Box::new(body),
        typ: todo_function_type(),
    })
}

impl Context {
    fn cps(&mut self, ast: &Ast, k: Ast) -> Ast {
        match ast {
            l @ Ast::Literal(_) => make_call(k, vec![l.clone()]),
            v @ Ast::Variable(_) => make_call(k, vec![v.clone()]),
            Ast::Lambda(lambda) => self.cps_lambda(lambda),
            Ast::FunctionCall(call) => {
                match call.function.as_ref() {
                    Ast::Lambda(lambda) => self.cps_call_lambda(lambda, &call, k),
                    _ => self.cps_call(&call, k),
                }
            }
            Ast::Definition(_) => todo!(),
            Ast::If(_) => todo!(),
            Ast::Match(_) => todo!(),
            Ast::Return(return_expr) => self.cps(&return_expr.expression, k),
            Ast::Sequence(_) => todo!(),
            Ast::Extern(_) => todo!(),
            Ast::Assignment(_) => todo!(),
            Ast::MemberAccess(access) => self.cps_member_access(access, k),
            Ast::Tuple(tuple) => self.cps_tuple(tuple, k),
            Ast::ReinterpretCast(_) => todo!(),
            Ast::Builtin(_) => todo!(),
        }
    }

    fn make_id_function(&mut self) -> Ast {
        self.next_variable_id += 1;
        let initial_k_arg = DefinitionInfo {
            definition: None,
            definition_id: DefinitionId(self.next_variable_id),
            name: None,
        };
        Ast::Lambda(Lambda {
            args: vec![initial_k_arg.clone()],
            body: Box::new(Ast::Variable(initial_k_arg)),
            typ: todo_function_type(),
        })
    }

    fn fresh_var(&mut self) -> Variable {
        self.next_variable_id += 1;
        DefinitionInfo {
            definition: None,
            definition_id: DefinitionId(self.next_variable_id),
            name: None,
        }
    }

    fn cps_lambda(&mut self, lambda: &Lambda) -> Ast {
        let new_k_arg = self.fresh_var();
        let mut args = lambda.args.clone();
        args.push(new_k_arg.clone());

        let body = Box::new(self.cps(&lambda.body, Ast::Variable(new_k_arg)));
        let typ = lambda.typ.clone();

        Ast::Lambda(Lambda { args, body, typ })
    }

    // cps k (Apply (Lambda param body) arg) = do
    //   body' <- cps k body
    //   let karg = Lambda param body'
    //   cps karg arg
    fn cps_call_lambda(&mut self, lambda: &Lambda, call: &FunctionCall, k: Ast) -> Ast {
        let body = self.cps(&lambda.body, k);
        let mut karg = body;

        for (param, arg) in lambda.args.iter().rev().zip(call.args.iter().rev()) {
            karg = make_lambda(param.clone(), karg);
            karg = self.cps(arg, karg)
        }

        karg
    }

    // cps k (Apply f x) = do
    //   fname <- next "f"
    //   xname <- next "x"
    //   let kx = Lambda xname $ Apply (Apply (Variable fname) (Variable xname)) k
    //   x' <- cps kx x
    //   let kf = Lambda fname x'
    //   cps kf f
    fn cps_call(&mut self, call: &FunctionCall, mut k: Ast) -> Ast {
        let fresh_function_name = self.fresh_var();
        let fresh_arg_names = fmap(&call.args, |_| self.fresh_var());

        let mut fresh_args = fmap(&fresh_arg_names, |arg| Ast::Variable(arg.clone()));
        fresh_args.push(k);

        k = make_call(Ast::Variable(fresh_function_name.clone()), fresh_args);

        for (arg_name, arg) in fresh_arg_names.into_iter().rev().zip(call.args.iter().rev()) {
            k = make_lambda(arg_name, k);
            k = self.cps(arg, k)
        }

        k = make_lambda(fresh_function_name, k);
        self.cps(&call.function, k)
    }

    fn cps_member_access(&mut self, access: &crate::hir::MemberAccess, k: Ast) -> Ast {
        // todo
        self.cps(&access.lhs, k)
    }

    fn cps_tuple(&mut self, tuple: &crate::hir::Tuple, mut k: Ast) -> Ast {
        let fresh_arg_names = fmap(&tuple.fields, |_| self.fresh_var());
        let fresh_args = fmap(&fresh_arg_names, |arg| Ast::Variable(arg.clone()));

        k = make_call(k, vec![Ast::Tuple(Tuple { fields: fresh_args })]);

        for (name, field) in fresh_arg_names.into_iter().rev().zip(tuple.fields.iter().rev()) {
            k = make_lambda(name, k);
            k = self.cps(field, k)
        }

        k
    }
}
