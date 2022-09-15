use crate::lexer::{self, lex};

/// An S-Expressions is a Symbolic Expression.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum SExpression {
    /// An Atom is called an "atomic symbol" in McCarthy's 1960 article.
    /// Unlike that article we do not allow spaces in atom names.
    ATOM(String),
    /// A Pair is a dotted pair in McCarthy's article. We use spaces to separate the elements rather than a dot.
    PAIR(Box<SExpression>, Box<SExpression>),
}

/// An M-Expression is a meta-expression over S-Expressions.
/// McCarthy used a special syntax for these, *e.g.* `car[x]` or `car[cons[(A · B); x]]`.
/// Later Lisps generally use the S-expression syntax for theses, e.g. `(car x)` and `(car (cons ((A B) x)))`.
#[derive(Eq, PartialEq, Debug)]
pub enum MExpression {
    /// The `atom`  predicate returns true (`T`) or false (`T`) dependening on whether `x` is an atomic symbol or not.
    /// McCarthy: `atom[x]` has the value of `T` or `F` according to whether `x` is an atomic symbol. Thus `atom [X] = T` and `atom [(X · A)] = F`.
    /// Later Lisps often add a trailing `p` or a question mark to predicate functions, *e.g.* `ATOMP` or `atom?`
    ATOM(SExpression),

    /// CAR is a homomorphic function on S-expressions, itself an S-expression. It evaluates to the first element of a pair.
    CAR(Box<SExpression>),
    /// CDR is a homomorphic function on S-expressions, itself an S-expression. It evaluates to the second element of a pair.
    CDR(Box<SExpression>),

    COND(Box<SExpression>),
    CONS(Box<SExpression>, Box<SExpression>),
    EQ(Box<SExpression>, Box<SExpression>),
    /// Quote is an extension over the original six Lisp axioms
    QUOTE(Box<SExpression>),
}

/// A parsed Lisp expression. The AST is built from S-Expression primitives and M-Expressions (functions over S-Expressions).
#[derive(Eq, PartialEq, Debug)]
pub enum LispExpr {
    /// A symbolic expression (S-Expression).
    SExpr(SExpression),
    /// An meta-expression (M-Expression) is a function name and its arguments.
    MExpr(String, Vec<LispExpr>),
}

/// Syntax error
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum SyntaxError {
    EndOfFile(String),
    EndOfFileExpected(String, Vec<lexer::Lexeme>),
    InvalidCharacter(char),
    MisplacedLexeme(String, lexer::Lexeme),
    SExpressionExpected(String),
    MalformedMExpression(String, Box<SyntaxError>),
    MalformedListExpression(String, Box<SyntaxError>),
}

fn unparse_to(expr: &LispExpr, mut out: String) -> String {
    match expr {
        LispExpr::SExpr(sexpr) => match sexpr {
            SExpression::ATOM(s) => {
                out.push_str(s);
            }
            _ => todo!("unparse for S-Expression not fully implemented"),
        },
        LispExpr::MExpr(_, _) => {
            todo!("unparse for M-Expressions not implemented");
        }
    }
    out
}

//        MExpression::QUOTE(inner) => {
//            out.push_str("'");
//            out.push_str(&unparse(inner));
//        }

/// Convert an abstract syntax tree (AST) into its corresponding Lisp code as a string.
pub fn unparse(expr: &LispExpr) -> String {
    let result = unparse_to(expr, String::from(""));
    result
}

/// Alias for the lexer
type PeekableLexer<'a> = std::iter::Peekable<lexer::Lexer<'a>>;

/// Parse until the sentinel lexeme is found.
/// Consumes the sentinel.
/// Returns the parsed expressions and the next state of the lexer.
fn parse_until<'a>(sentinel: &lexer::Lexeme, lexer: PeekableLexer<'a>) -> (Result<Vec<LispExpr>, SyntaxError>, PeekableLexer<'a>) {
    let mut result = vec![];
    let mut l = lexer;
    while l.next_if_eq(sentinel).is_none() {
        // sentinel lexeme not reached, capture all arguments
        let (arg, l_next) = parse_next(l);
        l = l_next;
        match arg {
            Ok(a) => {
                result.push(a);
            }
            Err(err) => {
                let msg = match err {
                    SyntaxError::EndOfFile(_) => "Syntax error in expression. Expected expression or closing lexeme. Got end of file.",
                    _ => "Syntax error in expression"
                };
                return (
                    Err(SyntaxError::MalformedListExpression(
                        String::from(msg),
                        Box::new(err),
                    )),
                    l,
                );
            }
        }
    }
    (Ok(result), l)
}

/// Parse an S-Expression from the lexer.
fn parse_sexpr<'a>(mut lexer: PeekableLexer<'a>) -> (Result<SExpression, SyntaxError>, PeekableLexer<'a>)
{
    match lexer.next() {
        None => (
            Err(SyntaxError::EndOfFile(String::from(
                "Syntax error: Expected S-expression, got end of file.",
            ))),
            lexer,
        ),
        Some(lexer::Lexeme::Invalid(ch)) => (Err(SyntaxError::InvalidCharacter(ch)), lexer),
        Some(lexer::Lexeme::RPar) => (
            Err(SyntaxError::MisplacedLexeme(
                String::from("Unmatched closing parenthesis."),
                lexer::Lexeme::RPar,
            )),
            lexer,
        ),
        Some(lexer::Lexeme::LPar) => {
            let mut inners = vec![];
            while lexer.next_if_eq(&lexer::Lexeme::RPar).is_none() {
                let (result, l_next) = parse_sexpr(lexer);
                lexer = l_next;
                match result {
                    Ok(sexpr) => { inners.push(sexpr); }
                    Err(_) => { todo!("error in S-expression"); }
                }
            }
            match inners.len() {
                2 => {
                    (Ok(SExpression::PAIR(Box::new(inners[0].clone()), Box::new(inners[1].clone()))), lexer)
                }
                _ => {
                    todo!("malformed S-Expression")
                }
            }
        }
        Some(lexer::Lexeme::AlphaNum(s)) => {
            (Ok(SExpression::ATOM(String::from(s))), lexer)
        }
        _ => { todo!("invalid token in S-Expression") }
    }
}

fn parse_next<'a>(
    mut lexer: PeekableLexer<'a>,
) -> (
    Result<LispExpr, SyntaxError>,
    PeekableLexer<'a>,
) {
    let l = lexer.next();
    match l {
        None => (
            Err(SyntaxError::EndOfFile(String::from(
                "Syntax error: Expected S-expression, got end of file.",
            ))),
            lexer,
        ),
        Some(lexer::Lexeme::Invalid(ch)) => (Err(SyntaxError::InvalidCharacter(ch)), lexer),
        Some(lexer::Lexeme::RPar) => (
            Err(SyntaxError::MisplacedLexeme(
                String::from("Unmatched closing parenthesis."),
                lexer::Lexeme::RPar,
            )),
            lexer,
        ),
        Some(lexer::Lexeme::LPar) => {
            let (left, lexer) = parse_sexpr(lexer);
            match left {
                Err(SyntaxError::EndOfFile(_)) => (
                    Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as first element of pair. Got end of file."))), lexer),
                Err(_lerr) => (
                    Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as first element of pair."))), lexer),
                Ok(l) => {
                    let (right, mut lexer) = parse_sexpr(lexer);
                    let end_par = lexer.next();
                    // TODO: clean up or move these patterns to parse_sexpr
                    match (right, end_par) {
                        (Err(SyntaxError::InvalidCharacter(ch)), _) => (
                            Err(SyntaxError::SExpressionExpected(String::from(format!("Syntax error: Expected S-expression as second element of pair. Got invalid character: '{}'", ch)))), lexer),
                        (Err(_rerr), _) => (
                            Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as second element of pair."))),
                            lexer),
                        (Ok(r), Some(lexer::Lexeme::RPar)) => (
                            Ok(LispExpr::SExpr(SExpression::PAIR(Box::new(l), Box::new(r)))),
                            lexer,
                        ),
                        (_, Some(l)) => (
                            Err(SyntaxError::MisplacedLexeme(String::from("Syntax error: Expected closing parenthesis after second element of pair."), l.clone())), lexer),
                        (_, None) => (
                            Err(SyntaxError::EndOfFile(String::from("Syntax error: Expected closing parenthesis after second element of pair, got end of file."))), lexer),
                    }
                }
            }
        }
        Some(lexer::Lexeme::AlphaNum(s)) => {
            match lexer.next_if_eq(&lexer::Lexeme::LBracket) {
                Some(_) => {
                    // name then left bracket => M-Expression
                    let (args, l_next) = parse_until(&lexer::Lexeme::RBracket, lexer);
                    match args {
                        Ok(exprs) => (Ok(LispExpr::MExpr(s, exprs)), l_next),
                        Err(err) => {
                            let (msg, cause) = match &err {
                                SyntaxError::MalformedListExpression(_, inner) => {
                                    match **inner {
                                        SyntaxError::EndOfFile(_) => ("Syntax error in M-Expression: Expected S-Expression or closing bracket. Got end of file.",
                                                                      (**inner).clone()
                                                                      //SyntaxError::EndOfFile(String::from("Syntax error: unexpected end of file."))
                                        ),
                                        _ => ("Syntax error in M-Expression", err)
                                    }
                                }
                                _ => ("Syntax error in M-Expression", err)
                            };
                            return (
                                Err(SyntaxError::MalformedMExpression(
                                    String::from(msg),
                                    Box::new(cause),
                                )),
                                l_next,
                            );
                        }
                    }
                }
                None => {
                    // No bracket following alphanumeric string => S-Expression
                    (Ok(LispExpr::SExpr(SExpression::ATOM(s))), lexer)
                }
            }
        }
        _ => {
            todo!("not implemented yet");
        }
    }
}

/// Parse a string into an Expr representing its abstract syntax tree.
pub fn parse(input: &str) -> Result<LispExpr, SyntaxError> {
    let lexemes = lex(input).peekable();
    let (result, lexer) = parse_next(lexemes);
    let remaining: Vec<lexer::Lexeme> = lexer.collect();
    match (&result, remaining.is_empty()) {
        (Err(_), _) => result,
        (Ok(_), true) => result,
        (Ok(_), false) => Err(SyntaxError::EndOfFileExpected(
            String::from("Syntax error: Expected end of file."),
            remaining,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unparse_atom_string() {
        let expr = LispExpr::SExpr(SExpression::ATOM(String::from("FOO")));
        let actual = unparse(&expr);
        assert_eq!("FOO", actual);
    }

    #[test]
    fn unparse_atom_string_number() {
        let expr = LispExpr::SExpr(SExpression::ATOM(String::from("FOO1")));
        let actual = unparse(&expr);
        assert_eq!("FOO1", actual);
    }

    /*
        #[test]
        fn unparse_quoted_expr() {
            let expr = SExpression::QUOTE(Box::new(SExpression::ATOM(String::from("foo"))));
            let actual = unparse(&expr);
            assert_eq!("'foo", actual);
        }
    */

    #[test]
    fn parse_atom() {
        let actual = parse("AB");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(String::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_atom_string() {
        let actual = parse("AB");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(String::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_atom_string_and_number() {
        let actual = parse("A1");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(String::from("A1")))),
            actual
        );
    }

    #[test]
    fn parse_atom_with_trailing_whitespace() {
        let actual = parse("AB  ");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(String::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_invalid_value_blank() {
        let actual = parse("");
        assert_eq!(
            Err(SyntaxError::EndOfFile(String::from(
                "Syntax error: Expected S-expression, got end of file."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_empty_parens() {
        let actual = parse("()");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as first element of pair."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_missing_close() {
        let actual = parse("(");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as first element of pair. Got end of file."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_duplicate_close() {
        let actual = parse("(A B))");
        assert_eq!(
            Err(SyntaxError::EndOfFileExpected(
                String::from("Syntax error: Expected end of file."),
                vec![lexer::Lexeme::RPar],
            )),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_second_element_missing() {
        let actual = parse("(A)");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as second element of pair."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_dotted_pair() {
        // Note, unlike the McCarthy paper we do no allow space in the identifier names, so we don't need the dotted pairs.
        let actual = parse("(A . B)");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as second element of pair. Got invalid character: '.'"
            ))),
            actual
        );
    }

    // An S-expression is then simply an ordered pair, the terms of which may be
    // atomic symbols or simpler S-expressions

    // Pair of only atoms
    #[test]
    fn parse_pair_of_atom_atom() {
        let actual = parse("(A B)");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::ATOM(String::from("A"))),
                Box::new(SExpression::ATOM(String::from("B"))),
            ))),
            actual
        );
    }

    // Pair of atom and S-expression
    #[test]
    fn parse_pair_of_pair_atom() {
        let actual = parse("((A B) C)");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("A"))),
                    Box::new(SExpression::ATOM(String::from("B"))),
                )),
                Box::new(SExpression::ATOM(String::from("C"))),
            ))),
            actual
        );
    }

    // Pair of atom and S-expression
    #[test]
    fn parse_pair_of_atom_pair() {
        let actual = parse("(A (B C))");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::ATOM(String::from("A"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("B"))),
                    Box::new(SExpression::ATOM(String::from("C"))),
                )),
            ), )),
            actual
        );
    }

    // Pair of two S-expressions
    #[test]
    fn parse_pair_of_pair_pair() {
        let actual = parse("((A B) (C D))");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("A"))),
                    Box::new(SExpression::ATOM(String::from("B"))),
                )),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("C"))),
                    Box::new(SExpression::ATOM(String::from("D"))),
                )),
            ))),
            actual
        );
    }

    // Parse the first elementary m-expression, atom (atom variant)
    #[test]
    fn parse_mexpr_atom_of_atom() {
        let actual = parse("atom[A]");
        assert_eq!(
            Ok(LispExpr::MExpr(
                String::from("atom"),
                vec![LispExpr::SExpr(SExpression::ATOM(String::from("A")))],
            )),
            actual
        );
    }

    // Parse the first elementary m-expression, atom (pair variant)
    #[test]
    fn parse_mexpr_atom_of_pair() {
        let actual = parse("atom[(A B)]");
        assert_eq!(
            Ok(LispExpr::MExpr(
                String::from("atom"),
                vec![LispExpr::SExpr(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("A"))),
                    Box::new(SExpression::ATOM(String::from("B"))),
                ))],
            )),
            actual
        );
    }

    // Parse the second elementary m-expression, eq
    // Note that unlike McCarthy we don't use semicolons to separate the arguments
    #[test]
    fn parse_mexpr_eq_of_atom_atom() {
        let actual = parse("eq[A B]");
        assert_eq!(
            Ok(LispExpr::MExpr(
                String::from("eq"),
                vec![
                    LispExpr::SExpr(SExpression::ATOM(String::from("A"))),
                    LispExpr::SExpr(SExpression::ATOM(String::from("B"))),
                ],
            )),
            actual
        );
    }

    // Test the error handling for malformed M-Expressions
    #[test]
    fn parse_mexpr_missing_close_bracket() {
        let actual = parse("eq[A B");
        assert_eq!(
            Err(SyntaxError::MalformedMExpression(String::from("Syntax error in M-Expression: Expected S-Expression or closing bracket. Got end of file."),
                                                  Box::new(SyntaxError::EndOfFile(String::from("Syntax error: Expected S-expression, got end of file."))))),
            actual
        );
    }
}
