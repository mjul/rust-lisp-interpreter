/// Lexer for Lisp
/// Very simple since we have only atoms (alphanumeric) and parenthesis.
#[derive(Debug, Eq, PartialEq)]
pub enum Lexeme {
    LPar,
    RPar,
    LBracket,
    RBracket,
    AlphaNum(String),
    Invalid(char),
}

/// State for the lexer
pub struct Lexer<'a> {
    //iter: core::str::SplitWhitespace<'a>,
    iter: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn skip_whitespace(&mut self) {
        while let Some(_) = self.iter.next_if(|&ch| ch.is_whitespace()) {
            // skip it
        }
    }
    fn lex_alphanumeric(&mut self) -> Option<Lexeme> {
        let mut result = String::new();
        while let Some(ch) = self.iter.next_if(|&ch| ch.is_alphanumeric()) {
            result.push(ch);
        }
        if result.is_empty() {
            None
        } else {
            Some(Lexeme::AlphaNum(result))
        }
    }

    fn lex_next(&mut self) -> Option<Lexeme> {
        self.skip_whitespace();
        if let Some(&ch) = self.iter.peek() {
            match ch {
                '(' => {
                    self.iter.next();
                    Some(Lexeme::LPar)
                }
                ')' => {
                    self.iter.next();
                    Some(Lexeme::RPar)
                }
                '[' => {
                    self.iter.next();
                    Some(Lexeme::LBracket)
                }
                ']' => {
                    self.iter.next();
                    Some(Lexeme::RBracket)
                }
                _ if ch.is_alphabetic() => self.lex_alphanumeric(),
                _ => {
                    self.iter.next();
                    Some(Lexeme::Invalid(ch))
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
    type Item = Lexeme;

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
        assert_eq!(Some(Lexeme::LPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_right_parenthesis() {
        let mut lexer = lex(")");
        assert_eq!(Some(Lexeme::RPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_left_bracket() {
        let mut lexer = lex("[");
        assert_eq!(Some(Lexeme::LBracket), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_right_bracket() {
        let mut lexer = lex("]");
        assert_eq!(Some(Lexeme::RBracket), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_ignore_whitespace_before_lexeme() {
        assert_eq!(Some(Lexeme::LPar), lex(" (").next());
        assert_eq!(Some(Lexeme::LPar), lex("  (").next());
    }

    #[test]
    fn lexer_must_ignore_whitespace_after_lexeme() {
        let mut sut = lex(") ");
        assert_eq!(Some(Lexeme::RPar), sut.next());
        assert_eq!(None, sut.next());

        let mut lexer = lex(")  ");
        assert_eq!(Some(Lexeme::RPar), lexer.next());
        assert_eq!(None, lexer.next());
    }

    #[test]
    fn lexer_must_recognize_alpha_single_char() {
        let mut sut = lex("A");
        assert_eq!(Some(Lexeme::AlphaNum(String::from("A"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_alpha_multiple_chars() {
        let mut sut = lex("ABC");
        assert_eq!(Some(Lexeme::AlphaNum(String::from("ABC"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_alphanumeric() {
        let mut sut = lex("ABC1");
        assert_eq!(Some(Lexeme::AlphaNum(String::from("ABC1"))), sut.next());
        assert_eq!(None, sut.next());
    }

    // TODO: no leading digit in alphanumeric

    #[test]
    fn lexer_must_recognize_alphanum_whitespace_alphanum() {
        // atoms must be whitespace-separated
        let mut sut = lex("A B");
        assert_eq!(Some(Lexeme::AlphaNum(String::from("A"))), sut.next());
        assert_eq!(Some(Lexeme::AlphaNum(String::from("B"))), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_recognize_lpar_alphanum_rpar() {
        // parens and atoms need no whitespace separation
        let mut sut = lex("(ABC)");
        assert_eq!(Some(Lexeme::LPar), sut.next());
        assert_eq!(Some(Lexeme::AlphaNum(String::from("ABC"))), sut.next());
        assert_eq!(Some(Lexeme::RPar), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_return_invalid_on_non_atom_non_paren_punctuation() {
        let mut sut = lex(".");
        assert_eq!(Some(Lexeme::Invalid('.')), sut.next());
        assert_eq!(None, sut.next());
    }

    #[test]
    fn lexer_must_return_invalid_on_non_atom_non_paren_curly() {
        let mut sut = lex("{");
        assert_eq!(Some(Lexeme::Invalid('{')), sut.next());
        assert_eq!(None, sut.next());
    }
}
