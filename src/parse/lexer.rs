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

impl<'source> Iterator for Lexer<'source> {
    type Item = Lexeme<'source>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.scan_next())
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

            _ => self.error("unexpected character"),
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
            return self.error("unterminated string");
        }

        self.advance(); // peek `"`
        self.make(Token::String)
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

    fn error<'msg>(&self, msg: &'msg str) -> Lexeme<'msg> {
        Lexeme {
            token: Token::Error,
            text: msg,
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
    match text {
        "and" => Token::And,
        "break" => Token::Break,
        "continue" => Token::Continue,
        "else" => Token::Else,
        "false" => Token::False,
        "func" => Token::Func,
        "if" => Token::If,
        "let" => Token::Let,
        "loop" => Token::Loop,
        "nil" => Token::Nil,
        "object" => Token::Object,
        "or" => Token::Or,
        "return" => Token::Return,
        "true" => Token::True,
        _ => Token::Identifier,
    }
}
