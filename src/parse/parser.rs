use std::iter::Peekable;
use std::num::ParseFloatError;
use std::str::Chars;

use itertools::{peek_nth, PeekNth};
use num_bigint::{BigInt, ParseBigIntError};
use tracing::{debug, instrument};

use crate::parse::ast::*;
use crate::parse::{Lexeme, LexemeOwned, Lexer, Token};

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

#[derive(thiserror::Error, Debug, Clone)]
pub enum ParseError {
    #[error("{0}")]
    Other(String),

    #[error("synatx error: {}", .0.text)]
    Lexer(LexemeOwned),

    #[error(transparent)]
    Syntax(#[from] SyntaxError),

    #[error(transparent)]
    ParseInt(ParseBigIntError),

    #[error(transparent)]
    ParseFloat(ParseFloatError),

    #[error(transparent)]
    InvalidPlace(PlaceError),
}

pub struct Parser<'source> {
    previous: Lexeme<'source>,
    lexer: PeekNth<Lexer<'source>>,
    errors: Vec<ParseError>,
    panicking: bool,
}

impl std::fmt::Debug for Parser<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Parser")
            .field("previous", &self.previous)
            .field("lexer", &"(...)")
            .field("errors", &format!("({} errors)", self.errors.len()))
            .field("panicking", &self.panicking)
            .finish()
    }
}

#[derive(thiserror::Error, Debug, Clone)]
#[error("syntax error: expected {:?}, got {:?}", expected, actual)]
pub struct SyntaxError {
    expected: Token,
    actual: Option<LexemeOwned>,
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

type Fallible<T> = Result<T, FailedParse>;

#[derive(Debug)]
struct FailedParse;

#[derive(Debug)]
enum Either<L, R> {
    L(L),
    R(R),
}

impl<L, R> Either<L, R> {
    fn map_l<F, T>(self, f: F) -> Either<T, R>
    where
        F: FnOnce(L) -> T,
    {
        match self {
            Either::L(l) => Either::L(f(l)),
            Either::R(r) => Either::R(r),
        }
    }

    fn map_r<F, T>(self, f: F) -> Either<L, T>
    where
        F: FnOnce(R) -> T,
    {
        match self {
            Either::L(l) => Either::L(l),
            Either::R(r) => Either::R(f(r)),
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
        loop {
            self.previous = self.lexer.next().expect("Lexer Iterator always emits Some");
            if self.previous.token != Token::Error {
                break;
            }
            self.error(ParseError::Lexer(self.previous.to_owned()));
        }
    }

    #[instrument(level = "trace", ret)]
    fn take(&mut self, token: Token) -> Option<Lexeme<'source>> {
        if self.check(token) {
            return self.lexer.next();
        }
        None
    }

    fn must_take(&mut self, token: Token) -> Fallible<Lexeme<'source>> {
        self.take(token).ok_or_else(|| {
            let err = ParseError::Syntax(SyntaxError {
                expected: token,
                actual: self.lexer.peek().map(|l| l.to_owned()),
            });
            self.error(err);
            FailedParse
        })
    }

    fn error(&mut self, err: ParseError) {
        debug!({ ?err }, "parse error");
        self.errors.push(err);
        self.panicking = true;
    }

    fn synchronize(&mut self) {
        debug!("synchronizing parser");
        self.panicking = false;

        while !self.check(Token::Eof) {
            // We just consumed a terminator, so we should be ready for another statement.
            match self.previous.token {
                Token::Semicolon | Token::RightBrace => return,
                _ => {}
            }

            // The next token could start a statement, so resume from here.
            match self.peek().token {
                Token::Func | Token::Let | Token::Loop | Token::If | Token::Return => return,
                _ => {}
            }

            // No obvious recovery, so keep going.
            self.advance();
            let prev = self.previous;
            let next = self.peek();
            debug!({ ?prev, ?next }, "advance");
        }
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret)]
    fn program(&mut self) -> Program {
        let mut decls = Vec::new();

        while !self.check(Token::Eof) {
            match self.declaration() {
                Ok(decl) => decls.push(decl),
                Err(_) => self.synchronize(),
            };
        }

        Program { decls }
    }

    #[instrument(level = "trace", ret)]
    fn block(&mut self) -> Fallible<Block> {
        let open = self.must_take(Token::LeftBrace)?;
        self.expr_block(open)
    }

    #[instrument(level = "trace", ret)]
    fn declaration(&mut self) -> Fallible<Declaration> {
        if let Some(decl) = self.decl_only()? {
            Ok(decl)
        } else {
            self.statement().map(Declaration::Statement)
        }
    }

    #[instrument(level = "trace", ret)]
    fn block_declaration(&mut self) -> Fallible<Either<Declaration, Expression>> {
        let either = self.decl_or_expr()?;
        Ok(either)
    }

    #[instrument(level = "trace", ret)]
    fn decl_or_expr(&mut self) -> Fallible<Either<Declaration, Expression>> {
        if let Some(decl) = self.decl_only()? {
            return Ok(Either::L(decl));
        }

        let either = self.stmt_or_expr()?;
        Ok(either.map_l(Declaration::Statement))
    }

    #[instrument(level = "trace", ret)]
    fn decl_only(&mut self) -> Fallible<Option<Declaration>> {
        if let Some(let_) = self.take(Token::Let) {
            self.decl_let(let_).map(Declaration::Let).map(Some)
        } else if let Some(func) = self.take(Token::Func) {
            self.decl_func(func).map(Declaration::Func).map(Some)
        } else {
            Ok(None)
        }
    }

    #[instrument(level = "trace", ret)]
    fn decl_let(&mut self, _kw: Lexeme<'_>) -> Fallible<Let> {
        let ident = self.must_take(Token::Identifier)?;
        let ident = Identifier::new(ident.text);

        // TODO: Allow declaring without a value for conditional init
        self.must_take(Token::Equal)?;

        let expr = self.expression()?;
        self.must_take(Token::Semicolon)?;

        Ok(Let { ident, expr })
    }

    #[instrument(level = "trace", ret)]
    fn decl_func(&mut self, _kw: Lexeme<'_>) -> Fallible<Func> {
        let ident = self.must_take(Token::Identifier)?;
        let ident = Identifier::new(ident.text);

        let open = self.must_take(Token::LeftParen)?;
        let params = self.parameters(open)?;

        let body = self.block()?;

        Ok(Func {
            ident,
            params,
            body,
        })
    }

    #[instrument(level = "trace", ret)]
    fn parameters(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<Identifier>> {
        let mut params = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightParen) {
                break;
            }

            let name = self.must_take(Token::Identifier)?;
            params.push(Identifier::new(name.text));

            if let Some(_sep) = self.take(Token::Comma) {
                continue;
            } else {
                self.must_take(Token::RightParen)?;
                break;
            }
        }

        Ok(params)
    }

    #[instrument(level = "trace", ret)]
    fn stmt_or_expr(&mut self) -> Fallible<Either<Statement, Expression>> {
        let expr = self.expression()?;

        if let Some(_semi) = self.take(Token::Semicolon) {
            let stmt = Statement::Expression(expr);
            Ok(Either::L(stmt))
        } else if let Some(_eq) = self.take(Token::Equal) {
            let place = Place::try_from(expr).map_err(|err| {
                self.error(ParseError::InvalidPlace(err));
                FailedParse
            })?;

            let expr = self.expression()?;

            self.must_take(Token::Semicolon)?;

            let stmt = Statement::Assignment(Assignment { place, expr });
            return Ok(Either::L(stmt));
        } else {
            Ok(Either::R(expr))
        }
    }

    #[instrument(level = "trace", ret)]
    fn statement(&mut self) -> Fallible<Statement> {
        let expr = self.expression()?;

        if let Some(_eq) = self.take(Token::Equal) {
            let place = Place::try_from(expr).map_err(|err| {
                self.error(ParseError::InvalidPlace(err));
                FailedParse
            })?;

            let expr = self.expression()?;

            self.must_take(Token::Semicolon)?;

            return Ok(Statement::Assignment(Assignment { place, expr }));
        }

        if !expr.self_terminating() {
            self.must_take(Token::Semicolon)?;
        }

        Ok(Statement::Expression(expr))
    }

    #[instrument(level = "trace", ret)]
    fn expression(&mut self) -> Fallible<Expression> {
        self.logic_or().map(Expression::LogicOr)
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret)]
    fn logic_or(&mut self) -> Fallible<LogicOr> {
        let first = self.logic_and()?;

        let mut rest = Vec::new();
        while let Some(_or) = self.take(Token::Or) {
            let next = self.logic_and()?;
            rest.push(next);
        }

        Ok(LogicOr { first, rest })
    }

    #[instrument(level = "trace", ret)]
    fn logic_and(&mut self) -> Fallible<LogicAnd> {
        let first = self.equality()?;

        let mut rest = Vec::new();
        while let Some(_and) = self.take(Token::And) {
            let next = self.equality()?;
            rest.push(next);
        }

        Ok(LogicAnd { first, rest })
    }

    #[instrument(level = "trace", ret)]
    fn equality(&mut self) -> Fallible<Equality> {
        let mut a = self.comparison().map(Equality::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.comparison()?;
                    a = $op(Box::new(a), b);
                    continue;
                }
            };
        }

        loop {
            op!(Token::EqualEqual, Equality::Eq);
            op!(Token::BangEqual, Equality::Ne);

            return Ok(a);
        }
    }

    #[instrument(level = "trace", ret)]
    fn comparison(&mut self) -> Fallible<Comparison> {
        let mut a = self.term().map(Comparison::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.term()?;
                    a = $op(Box::new(a), b);
                    continue;
                }
            };
        }

        loop {
            op!(Token::Greater, Comparison::Gt);
            op!(Token::GreaterEqual, Comparison::Ge);
            op!(Token::Less, Comparison::Lt);
            op!(Token::LessEqual, Comparison::Le);

            return Ok(a);
        }
    }

    #[instrument(level = "trace", ret)]
    fn term(&mut self) -> Fallible<Term> {
        let mut a = self.factor().map(Term::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.factor()?;
                    a = $op(Box::new(a), b);
                    continue;
                }
            };
        }

        loop {
            op!(Token::Plus, Term::Add);
            op!(Token::Minus, Term::Sub);

            return Ok(a);
        }
    }

    #[instrument(level = "trace", ret)]
    fn factor(&mut self) -> Fallible<Factor> {
        let mut a = self.unary().map(Factor::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.unary()?;
                    a = $op(Box::new(a), b);
                    continue;
                }
            };
        }

        loop {
            op!(Token::Star, Factor::Mul);
            op!(Token::Slash, Factor::Div);
            op!(Token::Percent, Factor::Rem);

            return Ok(a);
        }
    }

    #[instrument(level = "trace", ret)]
    fn unary(&mut self) -> Fallible<Unary> {
        enum Op {
            Neg,
            Not,
        }

        let mut ops = Vec::new();

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    ops.push($op);
                    continue;
                }
            };
        }

        loop {
            op!(Token::Minus, Op::Neg);
            op!(Token::Bang, Op::Not);

            break;
        }

        let mut a = self.call().map(Unary::Value)?;
        while let Some(op) = ops.pop() {
            a = match op {
                Op::Neg => Unary::Neg(Box::new(a)),
                Op::Not => Unary::Not(Box::new(a)),
            };
        }
        Ok(a)
    }

    #[instrument(level = "trace", ret)]
    fn call(&mut self) -> Fallible<Call> {
        let mut callee = self.primary().map(Call::Value)?;

        loop {
            if let Some(open) = self.take(Token::LeftParen) {
                // This will consume the matching `)`.
                let args = self.arguments(open)?;
                callee = Call::Call(Box::new(callee), args);
                continue;
            }

            if let Some(_open) = self.take(Token::LeftBracket) {
                let idx = self.expression()?;
                self.must_take(Token::RightBracket)?;
                callee = Call::Index(Box::new(callee), Box::new(idx));
                continue;
            }

            if let Some(_token) = self.take(Token::Dot) {
                let field = self.must_identifier()?;
                callee = Call::Field(Box::new(callee), field);
                continue;
            }

            break;
        }

        Ok(callee)
    }

    #[instrument(level = "trace", ret)]
    fn arguments(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<Expression>> {
        let mut args = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightParen) {
                break;
            }

            let expr = self.expression()?;
            args.push(expr);

            if let Some(_sep) = self.take(Token::Comma) {
                continue;
            } else {
                self.must_take(Token::RightParen)?;
                break;
            }
        }

        Ok(args)
    }

    #[instrument(level = "trace", ret)]
    fn primary(&mut self) -> Fallible<Primary> {
        if let Some(open) = self.take(Token::LeftBrace) {
            self.expr_block(open).map(Primary::Block)
        } else if let Some(if_) = self.take(Token::If) {
            self.expr_if(if_).map(Primary::If)
        } else {
            self.atom().map(Primary::Atom)
        }
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret)]
    fn atom(&mut self) -> Fallible<Atom> {
        if let Some(ident) = self.take(Token::Identifier) {
            Ok(Atom::Identifier(Identifier::new(ident.text)))
        } else {
            self.literal().map(Atom::Literal)
        }
    }

    #[instrument(level = "trace", ret)]
    fn must_identifier(&mut self) -> Fallible<Identifier> {
        let ident = self.must_take(Token::Identifier)?;
        Ok(Identifier::new(ident.text))
    }

    #[instrument(level = "trace", ret)]
    fn expr_block(&mut self, _open: Lexeme<'_>) -> Fallible<Block> {
        let mut decls = Vec::new();

        while !self.check(Token::Eof) && !self.check(Token::RightBrace) {
            match self.block_declaration() {
                Err(FailedParse) => self.synchronize(),

                Ok(Either::L(decl)) => decls.push(decl),

                Ok(Either::R(expr)) => {
                    if expr.self_terminating() && !self.check(Token::RightBrace) {
                        // There may be more code in this block.
                        let decl = Declaration::Statement(Statement::Expression(expr));
                        decls.push(decl);
                    } else {
                        // This expression does not get an implicit semicolon, so it must be at the
                        // end of the block.
                        self.must_take(Token::RightBrace)?;
                        return Ok(Block {
                            decls,
                            expr: Some(Box::new(expr)),
                        });
                    }
                }
            };
        }

        self.must_take(Token::RightBrace)?;
        Ok(Block { decls, expr: None })
    }

    #[instrument(level = "trace", ret)]
    fn expr_if(&mut self, _kw: Lexeme<'_>) -> Fallible<If> {
        let condition = self.expression()?;
        let consequent = self.block()?;

        let mut alternative = None;
        if let Some(_else) = self.take(Token::Else) {
            alternative = Some(self.block()?);
        }

        Ok(If {
            condition: Box::new(condition),
            consequent,
            alternative,
        })
    }

    #[instrument(level = "trace", ret)]
    fn literal(&mut self) -> Fallible<Literal> {
        if let Some(_nil) = self.take(Token::Nil) {
            Ok(Literal::Nil)
        } else if let Some(_false) = self.take(Token::False) {
            Ok(Literal::Boolean(false))
        } else if let Some(_true) = self.take(Token::True) {
            Ok(Literal::Boolean(true))
        } else if let Some(int) = self.take(Token::Integer) {
            self.integer(int.text)
        } else if let Some(float) = self.take(Token::Float) {
            self.float(float.text)
        } else if let Some(string) = self.take(Token::String) {
            let text = string.text;
            let content = text
                .strip_prefix('"')
                .expect("string literal starts with double-quote")
                .strip_suffix('"')
                .expect("string literal ends with double-quote");

            let value = unescape_string(content);
            Ok(Literal::String(value))
        } else {
            let msg = format!("expected literal value, got {:?}", self.peek());
            self.error(ParseError::Other(msg));
            Err(FailedParse)
        }
    }

    #[instrument(level = "trace", ret)]
    fn integer(&mut self, text: &str) -> Fallible<Literal> {
        text.parse::<BigInt>().map(Literal::Integer).map_err(|err| {
            self.error(ParseError::ParseInt(err));
            FailedParse
        })
    }

    #[instrument(level = "trace", ret)]
    fn float(&mut self, text: &str) -> Fallible<Literal> {
        text.parse::<f64>().map(Literal::Float).map_err(|err| {
            self.error(ParseError::ParseFloat(err));
            FailedParse
        })
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
