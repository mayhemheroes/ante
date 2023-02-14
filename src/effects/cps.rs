use crate::hir::DefinitionId;
use crate::hir::FunctionCall;
use crate::hir::DefinitionInfo;
use crate::hir::Ast;
use crate::hir::Lambda;

fn convert_to_cps(ast: Ast) -> Ast {
    let initial_k = make_id_function();
    let mut context = Context::default();
    context.cps(ast, initial_k)
}

#[derive(Default)]
struct Context {
    next_variable_id: u32,
}

fn make_id_function() -> Ast {
    let initial_k_arg = DefinitionInfo {
        definition: None,
        definition_id: todo!(),
        name: None,
    };
    Ast::Lambda(Lambda {
        args: vec![initial_k_arg.clone()],
        body: Box::new(Ast::Variable(initial_k_arg)),
        typ: todo!(),
    })
}

fn call(f: Ast, args: Vec<Ast>) -> Ast {
    Ast::FunctionCall(FunctionCall {
        function: Box::new(f),
        args,
        function_type: todo!()
    })
}

fn lambda(args: Vec<Variable>, body: Ast) -> Ast {
    Ast::Lambda(Lambda {
        args,
        body: Box::new(body),
        typ: todo!(),
    })
}

impl Context {
    fn cps(&mut self, ast: &Ast, k: Ast) -> Ast {
        match ast {
            l @ Ast::Literal(_) => call(k, vec![l]),
            v @ Ast::Variable(_) => call(k, vec![v]),
            Ast::Lambda(lambda) => self.cps_lambda(lambda),
            Ast::FunctionCall(call) => {
                match call.function.as_ref() {
                    Ast::Lambda(lambda) => self.cps_call_lambda(lambda, &call),
                    _ => self.cps_call(&call),
                }
            }
            Ast::Definition(_) => todo!(),
            Ast::If(_) => todo!(),
            Ast::Match(_) => todo!(),
            Ast::Return(_) => todo!(),
            Ast::Sequence(_) => todo!(),
            Ast::Extern(_) => todo!(),
            Ast::Assignment(_) => todo!(),
            Ast::MemberAccess(_) => todo!(),
            Ast::Tuple(_) => todo!(),
            Ast::ReinterpretCast(_) => todo!(),
            Ast::Builtin(_) => todo!(),
        }
    }

    fn fresh_var(&mut self) -> Ast {
        self.next_variable_id += 1;
        let id = self.next_variable_id;
        Ast::Variable(DefinitionInfo {
            definition: None,
            definition_id: DefinitionId(id),
            name: None,
        })
    }

    fn cps_lambda(&mut self, lambda: &Lambda) -> Ast {

    }

    // cps k (Apply (Lambda param body) arg) = do
    //   body' <- cps k body
    //   let karg = Lambda param body'
    //   cps karg arg
    fn cps_call_lambda(&mut self, lambda: &Lambda, call: &FunctionCall) -> Ast {
        let body = self.cps(&lambda.body, k);
        let karg = lambda(lambda.args.clone(), body);
        self.cps(arg, karg)
    }

    // cps k (Apply f x) = do
    //   fname <- next "f"
    //   xname <- next "x"
    //   let kx = Lambda xname $ Apply (Apply (Variable fname) (Variable xname)) k
    //   x' <- cps kx x
    //   let kf = Lambda fname x'
    //   cps kf f
    fn cps_call(&mut self, call: &FunctionCall) -> Ast {

    }
}
