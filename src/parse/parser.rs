use std::iter::Peekable;
use std::num::{ParseFloatError, ParseIntError};
use std::str::Chars;

use itertools::{peek_nth, PeekNth};

use crate::parse::ast::*;
use crate::parse::{Lexeme, Lexer, Token};

#[derive(thiserror::Error, Debug)]
pub struct ParseErrors(Vec<ParseError>);

impl std::fmt::Display for ParseErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(err) = self.0.first() {
            write!(f, "{}", err)?;
        } else {
            return write!(f, "");
        }

        for err in &self.0[1..] {
            write!(f, "\n{}", err)?;
        }
        Ok(())
    }
}

#[derive(thiserror::Error, Debug)]
pub enum ParseError {
    #[error("{0}")]
    Other(String),

    #[error(transparent)]
    ParseInt(ParseIntError),

    #[error(transparent)]
    ParseFloat(ParseFloatError),
}

pub struct Parser<'source> {
    previous: Lexeme<'source>,
    lexer: PeekNth<Lexer<'source>>,
    errors: Vec<ParseError>,
    panicking: bool,
}

impl<'source> Parser<'source> {
    fn new(source: &'source str) -> Self {
        let mut lexer = peek_nth(Lexer::new(source));
        Self {
            previous: *lexer.peek().expect("Lexer Iterator always emits Some"),
            lexer,
            errors: Vec::new(),
            panicking: false,
        }
    }

    pub fn parse(source: &'source str) -> Result<Program, ParseErrors> {
        let mut parser = Self::new(source);
        let program = parser.program();

        if parser.errors.is_empty() {
            Ok(program)
        } else {
            Err(ParseErrors(parser.errors))
        }
    }
}

impl<'source> Parser<'source> {
    fn peek(&mut self) -> &Lexeme<'source> {
        self.peek_nth(0)
    }

    fn peek_nth(&mut self, n: usize) -> &Lexeme<'source> {
        self.lexer
            .peek_nth(n)
            .expect("Lexer Iterator always emits Some")
    }

    fn check(&mut self, token: Token) -> bool {
        self.peek().token == token
    }

    fn advance(&mut self) {
        self.previous = self.lexer.next().expect("Lexer Iterator always emits Some");
    }

    fn take(&mut self, token: Token) -> Option<Lexeme<'source>> {
        if self.check(token) {
            return self.lexer.next();
        }
        None
    }

    fn error(&mut self, err: ParseError) {
        self.errors.push(err);
        self.panicking = true;
    }

    fn synchronize(&mut self) {
        self.panicking = false;

        while !self.check(Token::Eof) {
            // We just consumed a semicolon, so we should be ready for another statement.
            if self.previous.token == Token::Semicolon {
                return;
            }

            // The next token could start a statement, so resume from here.
            match self.peek().token {
                Token::Func | Token::Let | Token::Loop | Token::If | Token::Return => return,

                // No obvious recovery, so keep going.
                _ => self.advance(),
            }
        }
    }
}

impl<'source> Parser<'source> {
    fn program(&mut self) -> Program {
        let mut decls = Vec::new();

        while !self.check(Token::Eof) {
            match self.declaration() {
                Some(decl) => decls.push(decl),
                None => self.synchronize(),
            };
        }

        Program { decls }
    }

    fn declaration(&mut self) -> Option<Declaration> {
        self.statement().map(Declaration::Statement)
    }

    fn statement(&mut self) -> Option<Statement> {
        self.expression().map(Statement::Expression)
    }

    fn expression(&mut self) -> Option<Expression> {
        self.literal().map(Expression::Literal)
    }

    fn literal(&mut self) -> Option<Literal> {
        if let Some(_nil) = self.take(Token::Nil) {
            Some(Literal::Nil)
        } else if let Some(_false) = self.take(Token::False) {
            Some(Literal::Boolean(false))
        } else if let Some(_true) = self.take(Token::True) {
            Some(Literal::Boolean(true))
        } else if let Some(int) = self.take(Token::Integer) {
            match int.text.parse::<u64>() {
                Ok(value) => Some(Literal::Integer(value)),
                Err(err) => {
                    self.error(ParseError::ParseInt(err));
                    None
                }
            }
        } else if let Some(float) = self.take(Token::Float) {
            match float.text.parse::<f64>() {
                Ok(value) => Some(Literal::Float(value)),
                Err(err) => {
                    self.error(ParseError::ParseFloat(err));
                    None
                }
            }
        } else if let Some(string) = self.take(Token::String) {
            let text = string.text;
            let content = text
                .strip_prefix('"')
                .expect("string literal starts with double-quote")
                .strip_suffix('"')
                .expect("string literal ends with double-quote");

            let value = unescape_string(content);
            Some(Literal::String(value))
        } else {
            let msg = format!("expected literal value, got {:?}", self.peek());
            self.error(ParseError::Other(msg));
            None
        }
    }
}

fn unescape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\\' => out.extend(unescape_sequence(&mut chars).into_iter()),
            c => out.push(c),
        };
    }
    out
}

fn unescape_sequence(chars: &mut Peekable<Chars<'_>>) -> Vec<char> {
    let Some(ty) = chars.next() else {
        return Vec::new();
    };

    match ty {
        '"' => vec!['"'],
        '\'' => vec!['\''],
        '\\' => vec!['\\'],
        '0' => vec!['\0'],
        'n' => vec!['\n'],
        'r' => vec!['\r'],
        't' => vec!['\t'],
        'x' => unescape_ascii(chars),
        'u' => unescape_unicode(chars),

        // This was not a recognized escape sequence. Treat it as the literal text it was: a
        // backslash and whatever character came after.
        c => vec!['\\', c],
    }
}

fn unescape_ascii(chars: &mut Peekable<Chars<'_>>) -> Vec<char> {
    let mut taken = vec!['\\', 'x'];

    macro_rules! next_digit {
        () => {{
            let Some(c) = chars.next() else {
                return taken;
            };
            taken.push(c);

            let Some(d) = c.to_digit(16) else {
                return taken;
            };
            d
        }};
    }

    let hi = next_digit!();
    let lo = next_digit!();
    char::from_u32((hi << 4) | lo)
        .map(|c| vec![c])
        .unwrap_or(taken)
}

fn unescape_unicode(chars: &mut Peekable<Chars<'_>>) -> Vec<char> {
    let mut v = 0u32;
    let mut taken = vec!['\\', 'u'];

    macro_rules! next_digit {
        () => {{
            let Some(c) = chars.next() else {
                return taken;
            };
            taken.push(c);

            let Some(d) = c.to_digit(16) else {
                return taken;
            };
            d
        }};
    }

    macro_rules! peek {
        () => {{
            let Some(c) = chars.peek() else {
                return taken;
            };
            c
        }};
    }

    if peek!() != &'{' {
        return taken;
    }
    taken.push(chars.next().unwrap()); // peek {

    loop {
        if peek!() == &'}' {
            taken.push(chars.next().unwrap()); // peek }
            break;
        }

        // If there wasn't a closing brace after `\u{` + 6 digits, this escape sequence is invalid.
        // Treat it as literal text and restart the unescaping process.
        if taken.len() > 3 + 6 {
            return taken;
        }
        let d = next_digit!();
        v = (v << 4) | d;
    }

    char::from_u32(v).map(|c| vec![c]).unwrap_or(taken)
}
