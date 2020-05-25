use crate::lexer::{token::Token, Lexer};
use crate::error::location::Locatable;
use super::error::{ ParseError, ParseResult };

/// Helper macro for parser!
macro_rules! seq {
    // monadic bind:
    // 
    // name <- parser;
    // rest
    ( $input:ident $start:ident $location:tt => $name:tt <- $y:expr ; $($rem:tt)* ) => ({
        let ($input, $name) = $y($input)?;
        seq!($input $start $location => $($rem)*)
    });
    // trace point for debugging:
    // 
    // trace arg;
    // rest
    ( $input:ident $start:ident $location:tt => trace $arg:expr ; $($rem:tt)* ) => ({
        println!("trace {} - next = {:?}", $arg, $input.clone().next());
        seq!($input $start $location => $($rem)*)
    });
    // Mark the expression no backtracking for better errors:
    // 
    // name <-! parser;
    // rest
    ( $input:ident $start:ident $location:tt => $name:tt !<- $y:expr ; $($rem:tt)* ) => ({
        let ($input, $name) = no_backtracking($y)($input)?;
        seq!($input $start $location => $($rem)*)
    });
    // Finish the seq by wrapping in an Ok
    ( $input:ident $start:ident $location:tt => $expr:expr ) => ({
        let end = $input.locate();
        let $location = $start.union(end);
        Ok(($input, $expr))
    });
}

/// Defines a sequenced parser function with do-notation, threading
/// the input at each step and unwrapping the result with `?`.
/// In addition to `lhs <- rhs;` performing the monadic bind, there
/// is `lhs !<- rhs;` which is equivalent to `lhs <- no_backtracking(rhs);`.
/// The final expression given is wrapped in an `Ok((input, expr))`
///
/// for example:
/// ```
/// parser!(basic_definition loc =
///     name <- variable;
///     _ <- expect(Token::Equal);
///     value !<- expression;
///     Expr::definition(name, value, loc, ())
/// )
/// ```
macro_rules! parser {
    ( $name:ident $location:tt -> $return_type:ty = $($body:tt )* ) => {
        fn $name(input: Lexer) -> error::ParseResult<$return_type> {
            let start = input.locate();
            seq!(input start $location => $($body)*)
        }
    };
    // Variant with implicit return type of ParseResult<Ast>
    ( $name:ident $location:tt = $($body:tt )* ) => {
        parser!($name $location -> Ast = $($body)* );
    };
}

/// Matches the input if any of the given parsers matches.
/// This backtracks after each parse so for better error messages, no_backtracking
/// should be used in each contained parser once it is sure that parser's rule
/// should be matched. For example, in an if expression, everything after the initial `if`
/// should be marked as no_backtracking.
pub fn or<'a, It, T, F>(functions: It, rule: String) -> impl FnOnce(Lexer<'a>) -> ParseResult<'a, T> where
    It: IntoIterator<Item = F>,
    F: Fn(Lexer<'a>) -> ParseResult<'a, T>
{
    move |input| {
        for f in functions.into_iter() {
            match f(input.clone()) {
                Ok(c) => return Ok(c),
                Err(ParseError::Fatal(c)) => return Err(ParseError::Fatal(c)),
                _ => (),
            }
        }
        Err(ParseError::InRule(rule, input.locate()))
    }
}

/// Defines a parser that is just an `or` of other parsers, syntax is BNF:
/// `choice!(a_b_or_c = a | b | c);`
macro_rules! choice {
    ( $name:ident = $($body:tt )|* ) => {
        fn $name(input: Lexer) -> AstResult {
            self::or(&[
                $($body),*
            ], stringify!($name).to_string())(input)
        }
    };
}

/// Fail if the next token in the stream is not the given expected token
pub fn expect<'a>(expected: Token<'a>) -> impl Fn(Lexer<'a>) -> ParseResult<'a, Token<'a>> {
    use std::mem::discriminant;
    move |mut input| {
        match input.next() {
            Some(token) if discriminant(&expected) == discriminant(&token) => Ok((input, token)),
            _ => {
                let location = input.locate();
                Err(ParseError::Expected(vec![expected.clone()], location))
            }
        }
    }
}

/// Fail if the next token in the stream is not in the passed in array of expected tokens
pub fn expect_any<'a>(expected: &'a [Token<'a>]) -> impl Fn(Lexer<'a>) -> ParseResult<'a, Token<'a>> {
    move |mut input| {
        match input.next() {
            Some(token) if expected.into_iter().find(|tok| **tok == token).is_some() => Ok((input, token)),
            _ => {
                let location = input.locate();
                Err(ParseError::Expected(expected.iter().cloned().collect(), location))
            }
        }
    }
}

/// Matches the input 0 or 1 times. Only fails if a ParseError::Fatal is found
pub fn maybe<'a, F, T>(f: F) -> impl Fn(Lexer<'a>) -> ParseResult<'a, Option<T>>
    where F: Fn(Lexer<'a>) -> ParseResult<'a, T>
{
    move |input| {
        match f(input.clone()) {
            Ok((input, result)) => Ok((input, Some(result))),
            Err(ParseError::Fatal(err)) => Err(ParseError::Fatal(err)),
            Err(_) => Ok((input, None)),
        }
    }
}

/// Parse the two functions in a sequence, returning a pair of their results
pub fn pair<'a, F, G, FResult, GResult>(f: F, g: G) -> impl Fn(Lexer<'a>) -> ParseResult<'a, (FResult, GResult)> where
    F: Fn(Lexer<'a>) -> ParseResult<'a, FResult>,
    G: Fn(Lexer<'a>) -> ParseResult<'a, GResult>
{
    move |input| {
        let (input, fresult) = f(input)?;
        let (input, gresult) = g(input)?;
        Ok((input, (fresult, gresult)))
    }
}

/// Runs the parser 0 or more times until it errors, then returns a Vec of the successes.
/// Will only return Err when a ParseError::Fatal is found
pub fn many0<'a, T, F>(f: F) -> impl Fn(Lexer<'a>) -> ParseResult<'a, Vec<T>>
    where F: Fn(Lexer<'a>) -> ParseResult<'a, T>
{
    move |initial_input| {
        let mut input = initial_input.clone();
        let mut results = Vec::new();
        loop {
            match f(input.clone()) {
                Ok((lexer, t)) => {
                    input = lexer;
                    results.push(t);
                }
                Err(ParseError::Fatal(c)) => return Err(ParseError::Fatal(c)),
                _ => break,
            }
        }
        Ok((input, results))
    }
}

/// Runs the parser 1 or more times until it errors, then returns a Vec of the successes.
/// Will return Err if the parser fails the first time or a ParseError::Fatal is found
pub fn many1<'a, T, F>(f: F) -> impl Fn(Lexer<'a>) -> ParseResult<'a, Vec<T>>
    where F: Fn(Lexer<'a>) -> ParseResult<'a, T>
{
    move |initial_input| {
        let mut input = initial_input.clone();
        let mut results = Vec::new();

        match f(input.clone()) {
            Ok((lexer, t)) => {
                input = lexer;
                results.push(t);
            },
            Err(e) => return Err(e),
        }

        loop {
            match f(input.clone()) {
                Ok((lexer, t)) => {
                    input = lexer;
                    results.push(t);
                },
                Err(ParseError::Fatal(token)) => return Err(ParseError::Fatal(token)),
                Err(_) => break,
            }
        }
        Ok((input, results))
    }
}

/// Wraps the parser in a ParseError::Fatal if it fails. Used for better error reporting
/// around `or` and similar combinators to prevent backtracking away from an error.
pub fn no_backtracking<'a, T, F>(f: F) -> impl Fn(Lexer<'a>) -> ParseResult<'a, T>
    where F: Fn(Lexer<'a>) -> ParseResult<'a, T>
{
    move |input| {
        f(input).map_err(|e| match e {
            ParseError::Fatal(token) => ParseError::Fatal(token),
            err => ParseError::Fatal(Box::new(err)),
        })
    }
}

// Basic combinators for extracting the contents of a given token
pub fn identifier(mut input: Lexer) -> ParseResult<&str> {
    match input.next() {
        Some(Token::Identifier(name)) => Ok((input, name)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::Identifier("")], input.locate()))
        },
    }
}

pub fn string_literal_token(mut input: Lexer) -> ParseResult<String> {
    match input.next() {
        Some(Token::StringLiteral(contents)) => Ok((input, contents)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::StringLiteral("".to_owned())], input.locate()))
        },
    }
}

pub fn integer_literal_token(mut input: Lexer) -> ParseResult<u64> {
    match input.next() {
        Some(Token::IntegerLiteral(int)) => Ok((input, int)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::IntegerLiteral(0)], input.locate()))
        },
    }
}

pub fn float_literal_token(mut input: Lexer) -> ParseResult<f64> {
    match input.next() {
        Some(Token::FloatLiteral(float)) => Ok((input, float)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::FloatLiteral(0.0)], input.locate()))
        },
    }
}

pub fn char_literal_token(mut input: Lexer) -> ParseResult<char> {
    match input.next() {
        Some(Token::CharLiteral(contents)) => Ok((input, contents)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::CharLiteral(' ')], input.locate()))
        },
    }
}

pub fn bool_literal_token(mut input: Lexer) -> ParseResult<bool> {
    match input.next() {
        Some(Token::BooleanLiteral(boolean)) => Ok((input, boolean)),
        Some(Token::Invalid(c)) => {
            Err(ParseError::Fatal(Box::new(ParseError::LexerError(c, input.locate()))))
        },
        _ => {
            Err(ParseError::Expected(vec![Token::BooleanLiteral(true)], input.locate()))
        },
    }
}