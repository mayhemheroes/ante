use crate::cache::{ ModuleCache, DefinitionInfoId };
use crate::refine::context::RefinementContext;
use crate::error::location::Location;
use crate::util::fmap;
use crate::refine::z3;
use std::collections::BTreeSet;

impl<'c> RefinementContext<'c> {
    pub fn issue_refinement_error(&mut self, assert: z3::Ast,
        model: z3::Model, cache: &ModuleCache<'c>,
        assert_location: Location<'c>, origin: Location<'c>)
    {
        // Write the assert to a sexpr string, parse the string, then pretty-print it into
        // infix form
        let sexpr = self.z3_context.ast_to_string(assert);
        let (sexpr, variables, _) = parse_sexpr(&sexpr).unwrap();
        let assert = format!("`{}`", sexpr_to_string(&sexpr, cache));

        let definitions = variables.into_iter()
            .filter_map(|variable| self.get_z3_definition(variable, model, cache))
            .collect::<Vec<String>>()
            .join(", ");

        let context = if definitions.is_empty() {
            "".to_string()
        } else {
            format!(" with {}", definitions)
        };

        error!(assert_location, "Failed to prove {}{}", assert, context);
        note!(origin, "Refinement arises from condition here");
    }

    fn get_z3_definition(&mut self, id: DefinitionInfoId, model: z3::Model, cache: &ModuleCache<'c>) -> Option<String> {
        let info = &cache.definition_infos[id.0];
        let name = format!("{}${}", info.name, id.0);
        let typ = cache.follow_bindings(info.typ.as_ref().unwrap());

        // Filter out any functions used, giving their definition in error messages
        // usually isn't helpful
        if is_function(&typ) {
            return None;
        }

        let sort = self.type_to_sort(&typ, cache);
        let var = self.variable(&name, sort);
        self.z3_context.eval(model, var).map(|value| {
            let expr = z3_expr_to_string(self.z3_context, value, cache);
            format!("{} = {}", info.name, expr)
        })
    }
}

fn is_function(typ: &crate::types::Type) -> bool {
    use crate::types::Type::*;
    match typ {
        Function(..) => true,
        ForAll(_, typ) => {
            match typ.as_ref() {
                Function(..) => true,
                _ => false,
            }
        },
        _ => false,
    }
}

fn z3_expr_to_string<'c>(context: z3::Context, expr: z3::Ast, cache: &ModuleCache<'c>) -> String {
    let sexpr = context.ast_to_string(expr);
    let (sexpr, _, _) = parse_sexpr(&sexpr).unwrap();
    sexpr_to_string(&sexpr, cache)
}

type Variables = BTreeSet<DefinitionInfoId>;

#[derive(PartialEq, Eq)]
enum SExpr {
    List(Vec<SExpr>),
    Variable(DefinitionInfoId),
    Literal(String),
}

type ParserOutput<'input> = Option<(SExpr, Variables, &'input str)>;

fn parse_sexpr(input: &str) -> ParserOutput {
    let input = skip_spaces(input);

    if input.is_empty() {
        None
    } else if let Some((expr, variables, input)) = parse_list(input) {
        let input = skip_spaces(input);
        Some((expr, variables, input))
    } else if let Some((expr, variables, input)) = parse_literal(input) {
        let input = skip_spaces(input);
        Some((expr, variables, input))
    } else if let Some((expr, variables, input)) = parse_variable(input) {
        let input = skip_spaces(input);
        Some((expr, variables, input))
    } else {
        None
    }
}

fn parse_list(mut input: &str) -> ParserOutput {
    if !input.starts_with('(') {
        return None;
    }

    input = &input[1..];

    let mut exprs = vec![];
    let mut variables = BTreeSet::new();

    while let Some((expr, mut vars, rest_of_input)) = parse_sexpr(input) {
        exprs.push(expr);
        variables.append(&mut vars);
        input = rest_of_input;
    }

    if !input.starts_with(')') {
        return None;
    }

    if exprs[0] == SExpr::Literal("_".to_string()) {
        // This is a quoted z3 variable name in the format (_ quotedname 0)
        // this should be treated as a variable and not a list
        assert_eq!(exprs.len(), 3);
        Some((exprs.remove(1), variables, &input[1..]))
    } else {
        Some((SExpr::List(exprs), variables, &input[1..]))
    }
}

fn skip_spaces(input: &str) -> &str {
    let spaces = input.chars()
        .take_while(|c| c.is_whitespace())
        .collect::<String>();

    &input[spaces.len()..]
}

/// Parse a boolean, integer, or string literal.
/// Since these can't contain any variables, successfully
/// parsing these returns an empty Vec of variables and the
/// rest of the input string.
fn parse_literal(input: &str) -> ParserOutput {
    if input.starts_with("true") {
        Some((SExpr::Literal("true".to_string()), BTreeSet::new(), &input[4..]))
    } else if input.starts_with("false") {
        Some((SExpr::Literal("false".to_string()), BTreeSet::new(), &input[5..]))
    } else if input.starts_with('"') {
        match input[1..].find('"') {
            Some(end) => Some((SExpr::Literal(input[..end+1].to_string()), BTreeSet::new(), &input[end+1..])),
            None => unreachable!("Unclosed string delimiter while parsing refinements model"),
        }
    } else if (input.bytes().nth(0).unwrap() as char).is_numeric() {
        let length = input.bytes().take_while(|b| (*b as char).is_numeric()).count();
        Some((SExpr::Literal(input[..length].to_string()), BTreeSet::new(), &input[length..]))
    } else {
        None
    }
}

fn parse_variable(input: &str) -> ParserOutput {
    let mut name = input.chars()
        .take_while(|&c| c != '(' && c != ')' && !c.is_whitespace())
        .collect::<String>();

    if name.is_empty() {
        return None;
    }

    // We've successfully parsed a name, remember its length then try to parse the
    // DefinitionInfoId out of the name string
    let len = name.len();
    let mut variables = BTreeSet::new();

    // z3 sometimes inserts underscores around function calls with quoted names, filter them out
    if name == "_" {
        return Some((SExpr::Literal("_".to_string()), variables, &input[len..]));
    }

    // z3 sometimes wraps the name in |pipes| if it has special characters, remove them
    if name.starts_with('|') {
        assert_eq!(name.chars().last(), Some('|'));
        name.pop();
        name.remove(0);
    }

    match name.rfind('$') {
        Some(index) => {
            let suffix = name[index + 1 ..].parse().unwrap();
            let id = DefinitionInfoId(suffix);
            variables.insert(id);
            Some((SExpr::Variable(id), variables, &input[len..]))
        },
        None => Some((SExpr::Literal(name), variables, &input[len..]))
    }
}

fn sexpr_to_string<'c>(expr: &SExpr, cache: &ModuleCache<'c>) -> String {
    use SExpr::*;
    match expr {
        List(list) => {
            let mut exprs = fmap(list, |sexpr| sexpr_to_string(sexpr, cache));
            if exprs.len() == 3 {
                // Change equality to display as two equals ==
                if exprs[0] == "=" {
                    exprs[0].push('=');
                }
                format!("{} {} {}", exprs[1], exprs[0], exprs[2])
            } else {
                exprs.join(" ")
            }
        },
        Variable(id) => {
            let mut name = cache.definition_infos[id.0].name.clone();
            // If the name is a quoted operator, remove the quotes
            if name.starts_with("'") {
                name.remove(0);
                name.pop();
            }
            name
        }
        Literal(literal) => literal.clone(),
    }
}
