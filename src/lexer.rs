/// Lexter for Lisp
/// Very simple since we have atoms (alphanumeric) and parenthesis.
#[derive(Debug, Eq, PartialEq)]
pub enum Lexeme {
    LPar,
    RPar,
    AlphaNum(String),
}

/// State for the lexer
pub struct Lexer<'a> {
    //iter: core::str::SplitWhitespace<'a>,
    iter: std::iter::Peekable<std::str::Chars<'a>>,
}

impl<'a> Lexer<'a> {
    fn from(input: &'a str) -> Self {
        let iter = input.chars().peekable();
        Lexer { iter: iter }
    }

    fn lex_alphanumeric(&mut self) -> Option<Lexeme> {
        let mut result = String::new();
        while let Some(&ch) = self.iter.peek() {
            if ch.is_alphanumeric() {
                result.push(self.iter.next()?);
            } else {
                break;
            }
        }
        if result.is_empty() {
            None
        } else {
            Some(Lexeme::AlphaNum(result))
        }
    }

    fn lex_next(&mut self) -> Option<Lexeme> {
        if let Some(&ch) = self.iter.peek() {
            match ch {
                _ if ch.is_whitespace() => { self.iter.next(); self.lex_next() },
                '(' => { self.iter.next(); Some(Lexeme::LPar) },
                ')' => { self.iter.next(); Some(Lexeme::RPar) },
                _ => self.lex_alphanumeric()
            }
        } else {
            None
        }
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
        assert_eq!(Some(Lexeme::RPar), lex(")").next());
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

}