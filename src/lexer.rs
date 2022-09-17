//! Lexer for Lisp
//! Very simple since we have only atoms (alphanumeric) and parenthesis.

/// A Token represents the building blocks our language.
/// Definition: a **lexeme** is sequence of input characters that comprises a single token.
/// See _The Dragon Book_, Sec. 2.6, **p.** 54.
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum Token {
    /// Left parenthesis, `(`.
    LPar,
    /// Right parenthesis, `)`.
    RPar,
    /// Left bracket, `[`.
    LBracket,
    /// Right bracket, `]`.
    RBracket,
    /// Alpha-numerical token, the value is the lexeme.
    AlphaNum(String),
    Invalid(char),
}

/// State for the lexer
pub struct Lexer<'a> {
    iter: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn skip_whitespace(&mut self) {
        while let Some(_) = self.iter.next_if(|&ch| ch.is_whitespace()) {
            // skip it
        }
    }
    fn lex_alphanumeric(&mut self) -> Option<Token> {
        let mut result = String::new();
        while let Some(ch) = self.iter.next_if(|&ch| ch.is_alphanumeric()) {
            result.push(ch);
        }
        if result.is_empty() {
            None
        } else {
            Some(Token::AlphaNum(result))
        }
    }

    fn lex_next(&mut self) -> Option<Token> {
        self.skip_whitespace();
        if let Some(&ch) = self.iter.peek() {
            match ch {
                '(' => {
                    self.iter.next();
                    Some(Token::LPar)
                }
                ')' => {
                    self.iter.next();
                    Some(Token::RPar)
                }
                '[' => {
                    self.iter.next();
                    Some(Token::LBracket)
                }
                ']' => {
                    self.iter.next();
                    Some(Token::RBracket)
                }
                _ if ch.is_alphabetic() => self.lex_alphanumeric(),
                _ => {
                    self.iter.next();
                    Some(Token::Invalid(ch))
                }
            }
        } else {
            None
        }
    }
}

impl<'a> From<&'a str> for Lexer<'a> {
    fn from(input: &'a str) -> Self {
        let iter = input.chars().peekable();
        Lexer { iter }
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        self.lex_next()
    }
}

/// Tokenize a string into its lexemes.
pub fn lex(input: &str) -> Lexer {
    Lexer::from(input)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_must_recognize_left_parenthesis() {
        let mut lexer = lex("(");
        assert_eq!(Some(Token::LPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_right_parenthesis() {
        let mut lexer = lex(")");
        assert_eq!(Some(Token::RPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_left_bracket() {
        let mut lexer = lex("[");
        assert_eq!(Some(Token::LBracket), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_right_bracket() {
        let mut lexer = lex("]");
        assert_eq!(Some(Token::RBracket), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_ignore_whitespace_before_lexeme() {
        assert_eq!(Some(Token::LPar), lex(" (").next());
        assert_eq!(Some(Token::LPar), lex("  (").next());
    }

    #[test]
    fn lexer_must_ignore_whitespace_after_lexeme() {
        let mut sut = lex(") ");
        assert_eq!(Some(Token::RPar), sut.next());
        assert_eq!(None, sut.next());

        let mut lexer = lex(")  ");
        assert_eq!(Some(Token::RPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_alpha_single_char() {
        let mut sut = lex("A");
        assert_eq!(Some(Token::AlphaNum(String::from("A"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_alpha_multiple_chars() {
        let mut sut = lex("ABC");
        assert_eq!(Some(Token::AlphaNum(String::from("ABC"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_alphanumeric() {
        let mut sut = lex("ABC1");
        assert_eq!(Some(Token::AlphaNum(String::from("ABC1"))), sut.next());
        assert_eq!(None, sut.next());
    }

    // TODO: no leading digit in alphanumeric

    #[test]
    fn lexer_must_recognize_alphanum_whitespace_alphanum() {
        // atoms must be whitespace-separated
        let mut sut = lex("A B");
        assert_eq!(Some(Token::AlphaNum(String::from("A"))), sut.next());
        assert_eq!(Some(Token::AlphaNum(String::from("B"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_lpar_alphanum_rpar() {
        // parens and atoms need no whitespace separation
        let mut sut = lex("(ABC)");
        assert_eq!(Some(Token::LPar), sut.next());
        assert_eq!(Some(Token::AlphaNum(String::from("ABC"))), sut.next());
        assert_eq!(Some(Token::RPar), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_return_invalid_on_non_atom_non_paren_punctuation() {
        let mut sut = lex(".");
        assert_eq!(Some(Token::Invalid('.')), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_return_invalid_on_non_atom_non_paren_curly() {
        let mut sut = lex("{");
        assert_eq!(Some(Token::Invalid('{')), sut.next());
        assert_eq!(None, sut.next());
    }
}
