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
        if let Some(int) = self.take(Token::Integer) {
            match int.text.parse::<u64>() {
                Ok(value) => Some(Literal::Integer(value)),
                Err(err) => {
                    let msg = format!("invalid integer: {}", err);
                    self.error(ParseError::Other(msg));
                    None
                }
            }
        } else if let Some(float) = self.take(Token::Float) {
            match float.text.parse::<f64>() {
                Ok(value) => Some(Literal::Float(value)),
                Err(err) => {
                    let msg = format!("invalid float: {}", err);
                    self.error(ParseError::Other(msg));
                    None
                }
            }
        } else {
            let msg = format!("expected literal number, got {:?}", self.peek());
            self.error(ParseError::Other(msg));
            None
        }
    }
}
