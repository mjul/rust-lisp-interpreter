//! Parser for a Lisp language
use crate::lexer::{self, lex, LexerError, LexerResult};

/// An Atomic Symbol is a distinguishable string.
/// An "atomic symbol" is the building block of [SExpression].
#[derive(Eq, PartialEq, Debug, Clone)]
pub struct AtomicSymbol(String);

impl From<String> for AtomicSymbol {
    /// Construct an [AtomicSymbol] from this String.
    fn from(s: String) -> Self {
        // TODO: consider returning singletons for the special names NIL, T and F
        AtomicSymbol(s)
    }
}

impl From<&str> for AtomicSymbol {
    /// Construct an [AtomicSymbol] from this string.
    fn from(s: &str) -> Self {
        AtomicSymbol::from(String::from(s))
    }
}

/// An S-Expressions is a Symbolic Expression.
#[derive(Eq, PartialEq, Debug, Clone)]
pub enum SExpression {
    /// An Atom is called an "atomic symbol" in McCarthy's 1960 article.
    /// Unlike that article we do not allow spaces in atom names.
    ATOM(AtomicSymbol),
    /// A Pair is a dotted pair in McCarthy's article. We use spaces to separate the elements rather than a dot.
    PAIR(Box<SExpression>, Box<SExpression>),
}

impl SExpression {
    /// Create the special NIL atom
    pub fn new_nil() -> Self {
        SExpression::ATOM(AtomicSymbol::from("NIL"))
    }
    /// Create the special T (true) atom
    pub fn new_true() -> Self {
        SExpression::ATOM(AtomicSymbol::from("T"))
    }
    /// Create the special F (false) atom
    pub fn new_false() -> Self {
        SExpression::ATOM(AtomicSymbol::from("F"))
    }
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
    LexerError(String, Box<LexerError>),
    UnexpectedEndOfFile(String),
    EndOfFileExpected(String, Vec<LexerResult>),
    InvalidCharacter(char),
    MisplacedLexeme(String, lexer::Token),
    SExpressionExpected(String),
    MalformedSExpression(String, Box<SyntaxError>),
    MalformedMExpression(String, Box<SyntaxError>),
    MalformedListExpression(String, Box<SyntaxError>),
}

fn unparse_to(expr: &LispExpr, mut out: String) -> String {
    match expr {
        LispExpr::SExpr(sexpr) => match sexpr {
            SExpression::ATOM(AtomicSymbol(s)) => {
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
fn parse_until(
    sentinel: lexer::Token,
    lexer: PeekableLexer,
) -> (Result<Vec<LispExpr>, SyntaxError>, PeekableLexer) {
    let mut result = vec![];
    let mut l = lexer;
    let ok_sentinel = Ok(sentinel);
    while l.next_if_eq(&ok_sentinel).is_none() {
        // sentinel lexeme not reached, capture all arguments
        if l.peek().is_none() {
            // End of file
            return (
                Err(SyntaxError::UnexpectedEndOfFile(String::from(
                    "Unexpected end of file.",
                ))),
                l,
            );
        } else {
            let (arg, l_next) = parse_lispexpr(l);
            l = l_next;
            match arg {
                Ok(a) => {
                    result.push(a);
                }
                Err(err) => {
                    let msg = match err {
                        SyntaxError::UnexpectedEndOfFile(_) => {
                            "Expected expression or sentinel token."
                        }
                        _ => "Syntax error in expression.",
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
    }
    (Ok(result), l)
}

/// Determine if next lexeme is the beginning of an S-Expression.
fn is_beginning_of_sexpr(lexeme: Option<&LexerResult>) -> bool {
    // TODO: check casing
    match lexeme {
        Some(Ok(lexer::Token::AlphaNum(_))) => true,
        Some(Ok(lexer::Token::LPar)) => true,
        _ => false,
    }
}

/// Parse an S-Expression from the lexer.
/// Assumes that the ensuing tokens form an S-Expression and returns an error otherwise.
fn parse_sexpr(mut lexer: PeekableLexer) -> (Result<SExpression, SyntaxError>, PeekableLexer) {
    match lexer.next() {
        None => (
            Err(SyntaxError::UnexpectedEndOfFile(String::from(
                "Expected S-expression, got end of file.",
            ))),
            lexer,
        ),
        Some(Err(LexerError::InvalidCharacter(ch))) => {
            (Err(SyntaxError::InvalidCharacter(ch)), lexer)
        }
        Some(Ok(lexer::Token::RPar)) => (
            Err(SyntaxError::MisplacedLexeme(
                String::from("Unmatched closing parenthesis."),
                lexer::Token::RPar,
            )),
            lexer,
        ),
        Some(Ok(lexer::Token::LPar)) => {
            let mut inners = vec![];
            while is_beginning_of_sexpr(lexer.peek()) {
                let (result, l_next) = parse_sexpr(lexer);
                lexer = l_next;
                match result {
                    Ok(sexpr) => {
                        inners.push(sexpr);
                    }
                    Err(_) => {
                        todo!("error in S-expression");
                    }
                }
            }
            let closing_par = lexer.next();
            match closing_par {
                Some(Ok(lexer::Token::RPar)) => {
                    match inners.len() {
                        1 => {
                            // Shorthand (m) => (m, NIL)
                            (
                                Ok(SExpression::PAIR(
                                    Box::new(inners[0].clone()),
                                    Box::new(SExpression::new_nil()),
                                )),
                                lexer,
                            )
                        }
                        2 => (
                            Ok(SExpression::PAIR(
                                Box::new(inners[0].clone()),
                                Box::new(inners[1].clone()),
                            )),
                            lexer,
                        ),
                        _ => {
                            todo!("no support for S-Expression shorthand with many elements");
                        }
                    }
                }
                Some(Ok(t)) => (
                    Err(SyntaxError::MalformedSExpression(
                        String::from("Malformed S-Expression."),
                        Box::new(SyntaxError::MisplacedLexeme(
                            String::from("Expected closing parenthesis."),
                            t,
                        )),
                    )),
                    lexer,
                ),
                Some(Err(lerr)) => (
                    Err(SyntaxError::LexerError(
                        String::from("Expected closing parenthesis."),
                        Box::new(lerr),
                    )),
                    lexer,
                ),
                None => (
                    Err(SyntaxError::UnexpectedEndOfFile(String::from(
                        "Expected closing parenthesis, got end of file.",
                    ))),
                    lexer,
                ),
            }
        }
        Some(Ok(lexer::Token::AlphaNum(s))) => {
            (Ok(SExpression::ATOM(AtomicSymbol::from(s))), lexer)
        }
        _ => {
            todo!("invalid token in S-Expression")
        }
    }
}

/// Parse a [LispExpr] from the [Token] stream from the lexer.
/// Assumes that the next tokens form a valid [LispExpr] and returns an error if they do not.
fn parse_lispexpr(mut lexer: PeekableLexer) -> (Result<LispExpr, SyntaxError>, PeekableLexer) {
    let next_token = lexer.peek();
    match next_token {
        None => {
            lexer.next();
            (
                Err(SyntaxError::UnexpectedEndOfFile(String::from(
                    "Expected S-expression, got end of file.",
                ))),
                lexer,
            )
        }
        Some(Err(LexerError::InvalidCharacter(ch))) => {
            let bad_char = *ch;
            lexer.next();
            (Err(SyntaxError::InvalidCharacter(bad_char)), lexer)
        }
        Some(Ok(lexer::Token::RPar)) => {
            lexer.next();
            (
                Err(SyntaxError::MisplacedLexeme(
                    String::from("Unmatched closing parenthesis."),
                    lexer::Token::RPar,
                )),
                lexer,
            )
        }
        Some(Ok(lexer::Token::LPar)) => {
            lexer.next();
            let mut inners: Vec<SExpression> = vec![];
            let (result, mut lexer) = parse_until(lexer::Token::RPar, lexer);
            match result {
                Ok(exprs) => match &exprs[..] {
                    [] => (
                        Err(SyntaxError::SExpressionExpected(String::from(
                            "Expected S-expression as first element of pair.",
                        ))),
                        lexer,
                    ),
                    [LispExpr::SExpr(left)] => (
                        Err(SyntaxError::SExpressionExpected(String::from(
                            "Expected S-expression as second element of pair.",
                        ))),
                        lexer,
                    ),
                    /*[LispExpr::SExpr(left)] =>
                    (Ok(LispExpr::SExpr(SExpression::PAIR(
                        Box::new(left.clone()),
                        Box::new(SExpression::new_nil())))), lexer),*/
                    [LispExpr::SExpr(left), LispExpr::SExpr(right)] => (
                        Ok(LispExpr::SExpr(SExpression::PAIR(
                            Box::new(left.clone()),
                            Box::new(right.clone()),
                        ))),
                        lexer,
                    ),
                    _ => todo!("list shorthand"),
                },
                Err(e) => (
                    Err(SyntaxError::MalformedSExpression(
                        String::from("Invalid pair or list shorthand expression."),
                        Box::new(e),
                    )),
                    lexer,
                ),
            }
        }
        Some(Ok(lexer::Token::AlphaNum(s))) => {
            let lexeme = String::from(s);
            lexer.next();
            match lexer.next_if_eq(&Ok(lexer::Token::LBracket)) {
                Some(_) => {
                    // name then left bracket => M-Expression
                    let (args, l_next) = parse_until(lexer::Token::RBracket, lexer);
                    match args {
                        Ok(exprs) => (Ok(LispExpr::MExpr(lexeme, exprs)), l_next),
                        Err(SyntaxError::UnexpectedEndOfFile(msg)) => {
                            return (Err(SyntaxError::MalformedMExpression(
                                String::from("Syntax error in M-Expression: Expected S-Expression or closing bracket. Got end of file."),
                                Box::new(SyntaxError::UnexpectedEndOfFile(msg)))),
                                    l_next);
                        }
                        Err(err) => {
                            return (
                                Err(SyntaxError::MalformedMExpression(
                                    String::from("Syntax error in M-Expression"),
                                    Box::new(err),
                                )),
                                l_next,
                            );
                        }
                    }
                }
                None => {
                    // No bracket following alphanumeric string => S-Expression
                    (
                        Ok(LispExpr::SExpr(SExpression::ATOM(AtomicSymbol(lexeme)))),
                        lexer,
                    )
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
    let (result, lexer) = parse_lispexpr(lexemes);
    let remaining: Vec<LexerResult> = lexer.collect();
    match (&result, remaining.is_empty()) {
        (Err(_), _) => result,
        (Ok(_), true) => result,
        (Ok(_), false) => Err(SyntaxError::EndOfFileExpected(
            String::from("Expected end of file."),
            remaining,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unparse_atom_string() {
        let expr = LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("FOO")));
        let actual = unparse(&expr);
        assert_eq!("FOO", actual);
    }

    #[test]
    fn unparse_atom_string_number() {
        let expr = LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("FOO1")));
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
    fn atomic_symbol_from_must_be_implemented_for_string() {
        assert_eq!(
            AtomicSymbol(String::from("FOO")),
            AtomicSymbol::from(String::from("FOO"))
        );
    }

    #[test]
    fn atomic_symbol_from_must_be_implemented_for_str() {
        assert_eq!(AtomicSymbol(String::from("FOO")), AtomicSymbol::from("FOO"));
    }

    #[test]
    fn is_beginning_of_sexpr_is_true_for_alpha_and_left_paren() {
        assert_eq!(true, is_beginning_of_sexpr(Some(&Ok(lexer::Token::LPar))));
        assert_eq!(
            true,
            is_beginning_of_sexpr(Some(&Ok(lexer::Token::AlphaNum(String::from("AB")))))
        );
    }

    #[test]
    fn is_beginning_of_sexpr_is_false_for_others() {
        assert_eq!(false, is_beginning_of_sexpr(Some(&Ok(lexer::Token::RPar))));
        assert_eq!(
            false,
            is_beginning_of_sexpr(Some(&Ok(lexer::Token::RBracket)))
        );
        assert_eq!(
            false,
            is_beginning_of_sexpr(Some(&Ok(lexer::Token::LBracket)))
        );
        assert_eq!(
            false,
            is_beginning_of_sexpr(Some(&Ok(lexer::Token::RBracket)))
        );
    }

    #[test]
    fn parse_sexpr_must_parse_atom() {
        let mut lexer = lex("AB").peekable();
        let (actual, _) = parse_sexpr(lexer);
        assert_eq!(Ok(SExpression::ATOM(AtomicSymbol::from("AB"))), actual);
    }

    #[test]
    fn parse_sexpr_must_parse_pair_of_atom_atom() {
        let mut lexer = lex("(A B)").peekable();
        let (actual, _) = parse_sexpr(lexer);
        assert_eq!(
            Ok(SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
            )),
            actual
        );
    }

    #[test]
    fn parse_sexpr_must_parse_pair_of_atom_pair() {
        let mut lexer = lex("(A (B C))").peekable();
        let (actual, _) = parse_sexpr(lexer);
        assert_eq!(
            Ok(SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
                )),
            )),
            actual
        );
    }

    #[test]
    fn parse_sexpr_must_parse_pair_of_pair_atom() {
        let mut lexer = lex("((A B) C)").peekable();
        let (actual, _) = parse_sexpr(lexer);
        assert_eq!(
            Ok(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                )),
                Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
            )),
            actual
        );
    }

    #[test]
    fn parse_sexpr_must_parse_pair_of_pair_pair() {
        let mut lexer = lex("((A B) (C D))").peekable();
        let (actual, _) = parse_sexpr(lexer);
        assert_eq!(
            Ok(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                )),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("D"))),
                )),
            )),
            actual
        );
    }

    #[test]
    fn parse_atom() {
        let actual = parse("AB");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_atom_string() {
        let actual = parse("AB");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_atom_string_and_number() {
        let actual = parse("A1");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("A1")))),
            actual
        );
    }

    #[test]
    fn parse_atom_with_trailing_whitespace() {
        let actual = parse("AB  ");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("AB")))),
            actual
        );
    }

    #[test]
    fn parse_invalid_value_blank() {
        let actual = parse("");
        assert_eq!(
            Err(SyntaxError::UnexpectedEndOfFile(String::from(
                "Expected S-expression, got end of file."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_empty_parens() {
        let actual = parse("()");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Expected S-expression as first element of pair."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_missing_close() {
        let actual = parse("(");
        assert_eq!(
            Err(SyntaxError::MalformedSExpression(
                String::from("Invalid pair or list shorthand expression."),
                Box::new(SyntaxError::UnexpectedEndOfFile(String::from(
                    "Unexpected end of file."
                )))
            )),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_duplicate_close() {
        let actual = parse("(A B))");
        assert_eq!(
            Err(SyntaxError::EndOfFileExpected(
                String::from("Expected end of file."),
                vec![Ok(lexer::Token::RPar)],
            )),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_second_element_missing() {
        let actual = parse("(A)");
        assert_eq!(
            Err(SyntaxError::SExpressionExpected(String::from(
                "Expected S-expression as second element of pair."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_dotted_pair() {
        // Note, unlike the McCarthy paper we do no allow space in the identifier names, so we don't need the dotted pairs.
        let actual = parse("(A . B)");
        assert_eq!(
            Err(SyntaxError::MalformedSExpression(
                String::from("Invalid pair or list shorthand expression."),
                Box::new(SyntaxError::MalformedListExpression(
                    String::from("Syntax error in expression."),
                    Box::new(SyntaxError::InvalidCharacter('.'))
                ))
            )),
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
                Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
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
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                )),
                Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
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
                Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
                )),
            ),)),
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
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
                )),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("C"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("D"))),
                )),
            ))),
            actual
        );
    }

    // Pair in the shorthand syntax:
    // l. (m) stands for (m ·NIL).
    // 2. (m1, · · · , mn) stands for (m1 · (· · · (mn · NIL) · · ·)).
    // 3. (m1, · · · , mn · x) stands for (m1 · (· · · (mn · x) · · ·)).
    #[test]
    #[ignore]
    fn parse_pair_shorthand_one_element() {
        let actual = parse("(A)");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                Box::new(SExpression::ATOM(AtomicSymbol::from("NIL"))),
            ))),
            actual
        );
    }

    // 2. (m1, · · · , mn) stands for (m1 · (· · · (mn · NIL) · · ·)).
    #[test]
    #[ignore]
    fn parse_pair_shorthand_many_elements() {
        let actual = parse("(M1 M2 M3)");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("M1"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("M2"))),
                    Box::new(SExpression::PAIR(
                        Box::new(SExpression::ATOM(AtomicSymbol::from("M3"))),
                        Box::new(SExpression::ATOM(AtomicSymbol::from("NIL"))),
                    )),
                )),
            ))),
            actual
        );
    }

    // 3. (m1, · · · , mn · x) stands for (m1 · (· · · (mn · x) · · ·)).
    #[test]
    #[ignore]
    fn parse_pair_shorthand_many_elements_and_end() {
        let actual = parse("(M1 M2 M3 . X)");
        assert_eq!(
            Ok(LispExpr::SExpr(SExpression::PAIR(
                Box::new(SExpression::ATOM(AtomicSymbol::from("M1"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(AtomicSymbol::from("M2"))),
                    Box::new(SExpression::PAIR(
                        Box::new(SExpression::ATOM(AtomicSymbol::from("M3"))),
                        Box::new(SExpression::ATOM(AtomicSymbol::from("X"))),
                    )),
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
                vec![LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("A")))],
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
                    Box::new(SExpression::ATOM(AtomicSymbol::from("A"))),
                    Box::new(SExpression::ATOM(AtomicSymbol::from("B"))),
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
                    LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("A"))),
                    LispExpr::SExpr(SExpression::ATOM(AtomicSymbol::from("B"))),
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
                                                  Box::new(SyntaxError::UnexpectedEndOfFile(String::from("Unexpected end of file."))))),
            actual
        );
    }
}
