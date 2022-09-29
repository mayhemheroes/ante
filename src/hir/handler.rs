use std::collections::HashMap;

use crate::hir;
use crate::hir::DefinitionId;
use crate::util::fmap;
use crate::{cache::DefinitionInfoId, parser::ast};

use super::monomorphisation::Definition;
use super::{Ast, monomorphisation::Context};


pub(super) struct Handler {
    cases: HashMap<DefinitionInfoId, HandleCase>,
}

// Given:
// `handle ... | foo a b c -> body`
//
// args = `a b c`, and handle_branch = body
struct HandleCase {
    parameters: Vec<DefinitionId>,
    handle_branch: Ast,
    resume: DefinitionInfoId,
}

impl Handler {
    pub fn from_expr<'c>(monomorphiser: &mut Context<'c>, handle: &ast::Handle<'c>) -> Self {
        let cases = handle.branches.iter().zip(&handle.resumes).map(|((pattern, branch), resume)| {
            let (function, parameters) = store_parameters(monomorphiser, pattern);
            let case = HandleCase {
                parameters,
                handle_branch: monomorphiser.monomorphise(branch),
                resume: *resume,
            };
            (function, case)
        }).collect();

        Self { cases }
    }
}

impl<'c> Context<'c> {
    fn try_handle(&mut self, effect: DefinitionInfoId, args: &[ast::Ast<'c>], rest: &ast::Ast<'c>) {

    }
}

fn store_parameters<'c>(monomorphiser: &mut Context, pattern: &ast::Ast<'c>) -> (DefinitionInfoId, Vec<DefinitionId>) {
    // Name resolution should ensure all 'handle' patterns are function calls
    let call = match pattern {
        ast::Ast::FunctionCall(call) => call,
        _ => unreachable!(),
    };

    let function = match call.function.as_ref() {
        ast::Ast::Variable(variable) => variable.definition.unwrap(),
        // TODO: Verify: Is this actually unreachable?
        _ => unreachable!(),
    };

    let parameters = fmap(&call.args, |arg| {
        match arg {
            ast::Ast::Variable(arg) => {
                let id = arg.definition.unwrap();
                let definition_id = monomorphiser.next_unique_id();

                let name = Some(arg.to_string());
                let variable = hir::Variable { definition_id, definition: None, name };
                let definition = Definition::Normal(variable);

                let typ = monomorphiser.follow_all_bindings(arg.typ.as_ref().unwrap());
                monomorphiser.definitions.insert(id, typ, definition);
                definition_id
            },
            // The parser desugars any patterns more complex than variables to defer them to Match
            // expressions
            _ => unreachable!(),
        }
    });

    (function, parameters)
}
