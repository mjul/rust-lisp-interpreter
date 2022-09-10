use crate::lexer::{self, lex};

#[derive(Eq, PartialEq, Debug)]
pub enum SExpression {
    /// An Atom is called an "atomic symbol" in McCarthy's 1960 article.
    /// Unlike that article we do not allow spaces in atom names.
    ATOM(String),
    /// A Pair is a dotted pair in McCarthy's article. We use spaces to separate the elements rather than a dot.
    PAIR(Box<SExpression>, Box<SExpression>),

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

/// Syntax error
#[derive(Eq, PartialEq, Debug)]
pub enum SyntaxError {
    EndOfFile(String),
    EndOfFileExpected(String, Vec<lexer::Lexeme>),
    InvalidCharacter(char),
    MisplacedLexeme(String, lexer::Lexeme),
    SExpressionExpected(String),
}

fn unparse_to(expr: &SExpression, mut out: String) -> String {
    match expr {
        SExpression::ATOM(s) => {
            out.push_str(s);
        }
        SExpression::QUOTE(inner) => {
            out.push_str("'");
            out.push_str(&unparse(inner));
        }
        _ => out.push_str("not implemented"),
    }
    out
}

/// Convert an abstract syntax tree (AST) into a Lisp expression.
pub fn unparse(expr: &SExpression) -> String {
    let result = unparse_to(expr, String::from(""));
    result
}

fn parse_next<'a>(mut lexer: lexer::Lexer<'a>) -> (Result<SExpression, SyntaxError>, lexer::Lexer) {
    let l = lexer.next();
    match l {
        None => (
            Result::Err(SyntaxError::EndOfFile(String::from(
                "Syntax error: Expected S-expression, got end of file.",
            ))),
            lexer,
        ),
        Some(lexer::Lexeme::Invalid(ch)) => (Result::Err(SyntaxError::InvalidCharacter(ch)), lexer),
        Some(lexer::Lexeme::RPar) => (
            Result::Err(SyntaxError::MisplacedLexeme(
                String::from("Unmatched closing parenthesis."),
                lexer::Lexeme::RPar,
            )),
            lexer,
        ),
        Some(lexer::Lexeme::LPar) => {
            let (left, lexer) = parse_next(lexer);
            let (right, mut lexer) = parse_next(lexer);
            let end_par = lexer.next();
            match (left, right, end_par) {
                (Result::Err(SyntaxError::EndOfFile(_)), _, _) => (
                        Result::Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as first element of pair. Got end of file."))), lexer),
                (Result::Err(_lerr), _, _) => (
                        Result::Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as first element of pair."))), lexer),
                (_, Result::Err(SyntaxError::InvalidCharacter(ch)), _) => (
                        Result::Err(SyntaxError::SExpressionExpected(String::from(format!("Syntax error: Expected S-expression as second element of pair. Got invalid character: '{}'", ch)))), lexer),
                (_, Result::Err(_rerr), _) => (
                        Result::Err(SyntaxError::SExpressionExpected(String::from("Syntax error: Expected S-expression as second element of pair."))),
                    lexer),
                (Result::Ok(l), Result::Ok(r), Some(lexer::Lexeme::RPar)) => (
                    Result::Ok(SExpression::PAIR(Box::new(l), Box::new(r))),
                    lexer,
                ),
                (_, _, Some(l)) => (
                        Result::Err(SyntaxError::MisplacedLexeme(String::from("Syntax error: Expected closing parenthesis after second element of pair."), l)), lexer),
                (_, _, None) => (
                        Result::Err(SyntaxError::EndOfFile(String::from("Syntax error: Expected closing parenthesis after second element of pair, got end of file."))), lexer),
            }
        }
        Some(lexer::Lexeme::AlphaNum(s)) => (Result::Ok(SExpression::ATOM(s)), lexer),
    }
}

/// Parse a string with an S-Expression into an S-Expression abstract syntax tree.
pub fn parse(input: &str) -> Result<SExpression, SyntaxError> {
    let lexemes = lex(input);
    let (result, lexer) = parse_next(lexemes);
    let remaining: Vec<lexer::Lexeme> = lexer.collect();
    match (&result, remaining.is_empty()) {
        (Result::Err(_), _) => result,
        (Result::Ok(_), true) => result,
        (Result::Ok(_), false) => Result::Err(SyntaxError::EndOfFileExpected(
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
        let expr = SExpression::ATOM(String::from("FOO"));
        let actual = unparse(&expr);
        assert_eq!("FOO", actual);
    }

    #[test]
    fn unparse_atom_string_number() {
        let expr = SExpression::ATOM(String::from("FOO1"));
        let actual = unparse(&expr);
        assert_eq!("FOO1", actual);
    }

    #[test]
    fn unparse_quoted_expr() {
        let expr = SExpression::QUOTE(Box::new(SExpression::ATOM(String::from("foo"))));
        let actual = unparse(&expr);
        assert_eq!("'foo", actual);
    }

    #[test]
    fn parse_atom() {
        let actual = parse("AB");
        assert_eq!(Result::Ok(SExpression::ATOM(String::from("AB"))), actual);
    }

    #[test]
    fn parse_atom_string() {
        let actual = parse("AB");
        assert_eq!(Result::Ok(SExpression::ATOM(String::from("AB"))), actual);
    }

    #[test]
    fn parse_atom_string_and_number() {
        let actual = parse("A1");
        assert_eq!(Result::Ok(SExpression::ATOM(String::from("A1"))), actual);
    }

    #[test]
    fn parse_atom_with_trailing_whitespace() {
        let actual = parse("AB  ");
        assert_eq!(Result::Ok(SExpression::ATOM(String::from("AB"))), actual);
    }

    #[test]
    fn parse_invalid_value_blank() {
        let actual = parse("");
        assert_eq!(
            Result::Err(SyntaxError::EndOfFile(String::from(
                "Syntax error: Expected S-expression, got end of file."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_empty_parens() {
        let actual = parse("()");
        assert_eq!(
            Result::Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as first element of pair."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_missing_close() {
        let actual = parse("(");
        assert_eq!(
            Result::Err(SyntaxError::SExpressionExpected(String::from(
                "Syntax error: Expected S-expression as first element of pair. Got end of file."
            ))),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_unbalanced_parens_duplicate_close() {
        let actual = parse("(A B))");
        assert_eq!(
            Result::Err(SyntaxError::EndOfFileExpected(
                String::from("Syntax error: Expected end of file."),
                vec![lexer::Lexeme::RPar]
            )),
            actual
        );
    }

    #[test]
    fn parse_pair_invalid_value_second_element_missing() {
        let actual = parse("(A)");
        assert_eq!(
            Result::Err(SyntaxError::SExpressionExpected(String::from(
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
            Result::Err(SyntaxError::SExpressionExpected(String::from(
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
            Result::Ok(SExpression::PAIR(
                Box::new(SExpression::ATOM(String::from("A"))),
                Box::new(SExpression::ATOM(String::from("B")))
            )),
            actual
        );
    }

    // Pair of atom and S-expression
    #[test]
    fn parse_pair_of_pair_atom() {
        let actual = parse("((A B) C)");
        assert_eq!(
            Result::Ok(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("A"))),
                    Box::new(SExpression::ATOM(String::from("B")))
                )),
                Box::new(SExpression::ATOM(String::from("C")))
            )),
            actual
        );
    }

    // Pair of atom and S-expression
    #[test]
    fn parse_pair_of_atom_pair() {
        let actual = parse("(A (B C))");
        assert_eq!(
            Result::Ok(SExpression::PAIR(
                Box::new(SExpression::ATOM(String::from("A"))),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("B"))),
                    Box::new(SExpression::ATOM(String::from("C")))
                )),
            )),
            actual
        );
    }

    // Pair of two S-expressions
    #[test]
    fn parse_pair_of_pair_pair() {
        let actual = parse("((A B) (C D))");
        assert_eq!(
            Result::Ok(SExpression::PAIR(
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("A"))),
                    Box::new(SExpression::ATOM(String::from("B")))
                )),
                Box::new(SExpression::PAIR(
                    Box::new(SExpression::ATOM(String::from("C"))),
                    Box::new(SExpression::ATOM(String::from("D")))
                )),
            )),
            actual
        );
    }
}
