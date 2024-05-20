use tracing::instrument;

use crate::parse::{Lexeme, Token};

pub struct Lexer<'source> {
    source: &'source str,
    start: usize,
    current: usize,
    line: usize,
}

impl std::fmt::Debug for Lexer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Lexer")
            .field("source", &format!("({} bytes)", self.source.bytes().len()))
            .field("start", &self.start)
            .field("current", &self.current)
            .field("line", &self.line)
            .finish()
    }
}

pub struct Tokens<'source> {
    lexer: Lexer<'source>,
    done: bool,
}

impl<'source> Tokens<'source> {
    fn new(lexer: Lexer<'source>) -> Self {
        Self { lexer, done: false }
    }
}

impl<'source> Iterator for Tokens<'source> {
    type Item = Lexeme<'source>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let next = self.lexer.scan_next();
        if next.token == Token::Eof {
            self.done = true;
        }
        Some(next)
    }
}

pub struct TokensEndless<'source> {
    lexer: Lexer<'source>,
    eof: Option<Lexeme<'source>>,
}

impl<'source> TokensEndless<'source> {
    fn new(lexer: Lexer<'source>) -> Self {
        Self { lexer, eof: None }
    }
}

impl<'source> Iterator for TokensEndless<'source> {
    type Item = Lexeme<'source>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(eof) = self.eof {
            return Some(eof);
        }

        let next = self.lexer.scan_next();
        if next.token == Token::Eof {
            self.eof = Some(next);
        }
        Some(next)
    }
}

impl<'source> Lexer<'source> {
    pub fn new(source: &'source str) -> Self {
        Self {
            source,
            start: 0,
            current: 0,
            line: 1,
        }
    }

    /// Creates a consuming iterator that produces each token in the source.
    pub fn tokens(self) -> Tokens<'source> {
        Tokens::new(self)
    }

    /// Creates a consuming iterator that produces each token in the source. This
    /// version repeats the final EOF forever instead of returning None.
    pub fn tokens_endless(self) -> TokensEndless<'source> {
        TokensEndless::new(self)
    }

    #[instrument(level = "trace", ret)]
    pub fn scan_next(&mut self) -> Lexeme<'source> {
        self.skip_ignored();

        self.start = self.current;

        if self.at_eof() {
            return self.make(Token::Eof);
        }

        match self.advance() {
            // One character, no lookahead
            '(' => self.make(Token::LeftParen),
            ')' => self.make(Token::RightParen),
            '[' => self.make(Token::LeftBracket),
            ']' => self.make(Token::RightBracket),
            '{' => self.make(Token::LeftBrace),
            '}' => self.make(Token::RightBrace),
            ';' => self.make(Token::Semicolon),
            ',' => self.make(Token::Comma),
            '.' => self.make(Token::Dot),
            '-' => self.make(Token::Minus),
            '+' => self.make(Token::Plus),
            '/' => self.make(Token::Slash),
            '*' => self.make(Token::Star),
            '%' => self.make(Token::Percent),

            // One or two characters, 1 lookahead
            '!' => {
                if self.take('=') {
                    self.make(Token::BangEqual)
                } else {
                    self.make(Token::Bang)
                }
            }
            '=' => {
                if self.take('=') {
                    self.make(Token::EqualEqual)
                } else {
                    self.make(Token::Equal)
                }
            }
            '<' => {
                if self.take('=') {
                    self.make(Token::LessEqual)
                } else {
                    self.make(Token::Less)
                }
            }
            '>' => {
                if self.take('=') {
                    self.make(Token::GreaterEqual)
                } else {
                    self.make(Token::Greater)
                }
            }

            '"' => self.scan_string(),

            // TODO: Allow non-ASCII identifiers
            c if is_alpha(c) => self.scan_identifier(),
            c if is_digit(c) => self.scan_number(),

            _ => self.make(Token::ErrorUnrecognizedCharacter),
        }
    }

    fn skip_ignored(&mut self) {
        loop {
            match self.peek() {
                // Whitespace
                ' ' | '\r' | '\t' => {
                    self.advance();
                }
                '\n' => {
                    self.line += 1;
                    self.advance();
                }

                // Comments
                '/' => {
                    if self.peek_next() == '/' {
                        while self.peek() != '\n' && !self.at_eof() {
                            self.advance();
                        }
                    } else {
                        return;
                    }
                }

                _ => return,
            }
        }
    }

    fn scan_identifier(&mut self) -> Lexeme<'source> {
        while is_alpha(self.peek()) || is_digit(self.peek()) {
            self.advance();
        }

        let text = &self.source[self.start..self.current];

        let token = keyword_or_identifier(text);
        self.make(token)
    }

    fn scan_number(&mut self) -> Lexeme<'source> {
        while is_digit(self.peek()) {
            self.advance();
        }

        let mut has_fraction = false;

        // Only consume the dot if there are also more digits afterward. Otherwise, it indicates a
        // method call rather than a decimal number.
        if self.peek() == '.' && is_digit(self.peek_next()) {
            self.advance(); // `.`
            has_fraction = true;

            while is_digit(self.peek()) {
                self.advance();
            }
        }

        if has_fraction {
            self.make(Token::Float)
        } else {
            self.make(Token::Integer)
        }
    }

    fn scan_string(&mut self) -> Lexeme<'source> {
        // Multiline strings may change the current line. This Lexeme should contain the starting
        // line rather than the ending one.
        let line = self.line;

        while self.peek() != '"' && !self.at_eof() {
            if self.peek() == '\n' {
                self.line += 1;
            }

            // There are two escape sequences that have to be handled here in the lexer
            // because they would otherwise cause strings to terminate early:
            //
            //  1. `\"` escapes the double-quote, allowing the string to continue.
            //  2. `\\` escapes the backslash, preventing `\\"` from escaping the quote.
            //
            // All other escapes are interpreted during parsing.
            if self.peek() == '\\' && matches!(self.peek_next(), '"' | '\\') {
                self.advance(); // peek \
                self.advance(); // peek_next
            } else {
                self.advance(); // peek
            }
        }

        if self.at_eof() {
            return self.make(Token::ErrorUnterminatedString);
        }

        self.advance(); // peek `"`

        let mut lexeme = self.make(Token::String);
        lexeme.line = line;
        lexeme
    }

    fn at_eof(&self) -> bool {
        self.peek() == '\0'
    }

    fn peek(&self) -> char {
        self.source[self.current..]
            .chars()
            .next()
            .unwrap_or_default()
    }

    fn peek_next(&self) -> char {
        if self.at_eof() {
            return '\0';
        }

        let mut chars = self.source[self.current..].chars();
        chars.next().unwrap(); // peek 0
        chars.next().unwrap_or_default() // peek 1
    }

    fn advance(&mut self) -> char {
        let c = self.peek();
        self.current += c.len_utf8();
        c
    }

    fn take(&mut self, expected: char) -> bool {
        if self.at_eof() {
            return false;
        }

        if self.peek() != expected {
            return false;
        }

        self.advance();
        true
    }

    fn make(&self, token: Token) -> Lexeme<'source> {
        let text = &self.source[self.start..self.current];

        Lexeme {
            token,
            text,
            line: self.line,
        }
    }
}

fn is_alpha(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_'
}

fn is_digit(c: char) -> bool {
    c.is_ascii_digit()
}

fn keyword_or_identifier(text: &str) -> Token {
    Token::match_keyword(text).unwrap_or(Token::Identifier)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rstest::rstest;

    use crate::testing::snapshot_name;

    use super::Lexer;

    #[rstest]
    fn test_programs(#[files("test_programs/**/*.blis")] path: PathBuf) {
        let source = std::fs::read_to_string(&path).unwrap();
        let tokens: Vec<_> = Lexer::new(&source).tokens().collect();

        insta::with_settings!({
            input_file => &path,
            description => source.clone(),
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(snapshot_name(&path, "tokens"), tokens);
        })
    }

    #[test]
    fn test_special_characters() {
        let source = "*<<==!=>=>!+-*%/()[]{}:;,.";
        let tokens: Vec<_> = Lexer::new(source).tokens().collect();

        insta::with_settings!({
            description => source,
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(tokens);
        })
    }
}
