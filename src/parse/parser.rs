use std::num::ParseFloatError;
use std::str::Chars;

use itertools::{peek_nth, PeekNth};
use num_bigint::{BigInt, ParseBigIntError};
use serde::Serialize;
use tracing::{debug, instrument, trace};

use crate::parse::ast::*;
use crate::parse::lexer::TokensEndless;
use crate::parse::{Lexeme, LexemeOwned, Lexer, Token};

#[derive(thiserror::Error, Debug, Serialize)]
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

mod serde_ext {
    use std::num::ParseFloatError;

    use num_bigint::ParseBigIntError;
    use serde::ser::Serializer;

    pub fn serialize_parse_big_int_error<S: Serializer>(
        err: &ParseBigIntError,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        ser.serialize_str(&err.to_string())
    }

    pub fn serialize_parse_float_error<S: Serializer>(
        err: &ParseFloatError,
        ser: S,
    ) -> Result<S::Ok, S::Error> {
        ser.serialize_str(&err.to_string())
    }
}

#[derive(thiserror::Error, Debug, Clone, Serialize)]
pub enum ParseError {
    #[error("{0}")]
    Other(String),

    #[error("syntax error: {}", .0.text)]
    Lexer(LexemeOwned),

    #[error(transparent)]
    Syntax(#[from] SyntaxError),

    #[error(transparent)]
    #[serde(serialize_with = "serde_ext::serialize_parse_big_int_error")]
    ParseInt(ParseBigIntError),

    #[error(transparent)]
    #[serde(serialize_with = "serde_ext::serialize_parse_float_error")]
    ParseFloat(ParseFloatError),

    #[error(transparent)]
    InvalidPlace(PlaceError),
}

pub struct Parser<'source> {
    previous: Lexeme<'source>,
    tokens: PeekNth<TokensEndless<'source>>,
    errors: Vec<ParseError>,
    panicking: bool,
}

#[derive(thiserror::Error, Debug, Clone, Serialize)]
#[error("syntax error: expected {:?}, got {:?}", expected, actual)]
pub struct SyntaxError {
    expected: Token,
    actual: Option<LexemeOwned>,
}

impl<'source> Parser<'source> {
    fn new(source: &'source str) -> Self {
        let lexer = Lexer::new(source).tokens_endless();
        let mut tokens = peek_nth(lexer);
        Self {
            previous: *tokens.peek().expect("TokensEndless"),
            tokens,
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

    #[allow(unused)]
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
        self.tokens.peek_nth(n).expect("TokensEndless")
    }

    fn check(&mut self, token: Token) -> bool {
        self.peek().token == token
    }

    fn advance(&mut self) {
        loop {
            let prev = self.previous;
            let next = self.tokens.next().expect("TokensEndless");
            debug!({ ?prev, ?next }, "advance");

            self.previous = next;

            if self.previous.token.is_error() || self.previous.token == Token::Eof {
                break;
            }
            self.error(ParseError::Lexer(self.previous.to_owned()));
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn take(&mut self, token: Token) -> Option<Lexeme<'source>> {
        if self.check(token) {
            return self.tokens.next();
        }
        None
    }

    fn must_take(&mut self, token: Token) -> Fallible<Lexeme<'source>> {
        self.take(token).ok_or_else(|| {
            let err = ParseError::Syntax(SyntaxError {
                expected: token,
                actual: self.tokens.peek().map(|l| l.to_owned()),
            });
            self.error(err)
        })
    }

    fn error(&mut self, err: ParseError) -> FailedParse {
        debug!({ ?err }, "parse error");

        if !self.panicking {
            self.errors.push(err);
            self.panicking = true;
        }

        FailedParse
    }

    fn synchronize(&mut self) {
        debug!("synchronizing parser");

        while !self.check(Token::Eof) {
            // We just consumed a terminator, so we should be ready for another statement.
            match self.previous.token {
                Token::Semicolon | Token::RightBrace => {
                    return;
                }
                _ => {
                    trace!({ prev = ?self.previous }, "previous was not a terminator");
                }
            }

            // The next token could start a statement, so resume from here.
            let next = self.peek();
            match next.token {
                Token::Func
                | Token::If
                | Token::Let
                | Token::Loop
                | Token::Type
                | Token::Return => return,
                _ => {
                    trace!({ ?next }, "next is not a start keyword");
                }
            }

            // No obvious recovery, so keep going.
            self.advance();
        }

        self.panicking = false;
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret, skip(self))]
    fn program(&mut self) -> Program {
        let mut decls = Vec::new();

        while !self.check(Token::Eof) {
            match self.declaration() {
                Ok(decl) => decls.push(decl),
                Err(FailedParse) => self.synchronize(),
            };
        }

        Program { decls }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn block(&mut self) -> Fallible<Block> {
        let open = self.must_take(Token::LeftBrace)?;
        self.expr_block(open)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn declaration(&mut self) -> Fallible<Declaration> {
        if let Some(decl) = self.decl_only()? {
            Ok(decl)
        } else {
            self.statement().map(Declaration::Statement)
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn block_declaration(&mut self) -> Fallible<Either<Declaration, Expression>> {
        let either = self.decl_or_expr()?;
        Ok(either)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_or_expr(&mut self) -> Fallible<Either<Declaration, Expression>> {
        if let Some(decl) = self.decl_only()? {
            return Ok(Either::L(decl));
        }

        let either = self.stmt_or_expr()?;
        Ok(either.map_l(Declaration::Statement))
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_only(&mut self) -> Fallible<Option<Declaration>> {
        if let Some(kw) = self.take(Token::Type) {
            self.decl_struct(kw).map(Declaration::Type).map(Some)
        } else if let Some(kw) = self.take(Token::Func) {
            self.decl_func(kw).map(Declaration::Func).map(Some)
        } else if let Some(kw) = self.take(Token::Let) {
            self.decl_let(kw).map(Declaration::Let).map(Some)
        } else {
            Ok(None)
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_struct(&mut self, _kw: Lexeme<'_>) -> Fallible<Type> {
        let ident = self.must_identifier()?;

        // TODO(types): parse field specs here

        let methods = if let Some(_kw) = self.take(Token::With) {
            let open = self.must_take(Token::LeftBrace)?;
            self.type_methods(open)?
        } else {
            Vec::new()
        };

        Ok(Type { ident, methods })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn type_methods(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<Method>> {
        let mut methods = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightBrace) {
                break;
            }

            let kw = self.must_take(Token::Func)?;
            let m = self.decl_method(kw)?;
            methods.push(m);
        }

        Ok(methods)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_let(&mut self, _kw: Lexeme<'_>) -> Fallible<Let> {
        let ident = self.must_identifier()?;

        // TODO: Allow declaring without a value for conditional init
        self.must_take(Token::Equal)?;

        let expr = self.expression()?;
        self.must_take(Token::Semicolon)?;

        Ok(Let { ident, expr })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_method(&mut self, kw: Lexeme<'_>) -> Fallible<Method> {
        let mut self_ = false;
        if let Some(_kw) = self.take(Token::Self_) {
            self.must_take(Token::Dot)?;
            self_ = true;
        };

        let func = self.decl_func(kw)?;

        Ok(Method {
            self_,
            ident: func.ident,
            params: func.params,
            body: func.body,
        })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn decl_func(&mut self, _kw: Lexeme<'_>) -> Fallible<Func> {
        let ident = self.must_identifier()?;

        let open = self.must_take(Token::LeftParen)?;
        let params = self.parameters(open)?;

        let body = self.block()?;

        Ok(Func {
            ident,
            params,
            body,
        })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn parameters(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<Identifier>> {
        let mut params = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightParen) {
                break;
            }

            let param = self.must_identifier()?;
            params.push(param);

            if let Some(_sep) = self.take(Token::Comma) {
                continue;
            } else {
                self.must_take(Token::RightParen)?;
                break;
            }
        }

        Ok(params)
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret, skip(self))]
    fn statement(&mut self) -> Fallible<Statement> {
        if let Some(stmt) = self.stmt_kw()? {
            return Ok(stmt);
        }

        let expr = match self.assign_or_expr()? {
            Either::L(assignment) => return Ok(Statement::Assignment(assignment)),
            Either::R(expr) => expr,
        };

        if !expr.self_terminating() {
            self.must_take(Token::Semicolon)?;
        }

        Ok(Statement::Expression(expr))
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_or_expr(&mut self) -> Fallible<Either<Statement, Expression>> {
        if let Some(stmt) = self.stmt_kw()? {
            return Ok(Either::L(stmt));
        }

        let expr = match self.assign_or_expr()? {
            Either::L(assignment) => {
                let stmt = Statement::Assignment(assignment);
                return Ok(Either::L(stmt));
            }
            Either::R(expr) => expr,
        };

        if let Some(_semi) = self.take(Token::Semicolon) {
            let stmt = Statement::Expression(expr);
            Ok(Either::L(stmt))
        } else {
            Ok(Either::R(expr))
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_kw(&mut self) -> Fallible<Option<Statement>> {
        if let Some(kw) = self.take(Token::Break) {
            self.stmt_break(kw).map(Statement::Break).map(Some)
        } else if let Some(kw) = self.take(Token::Continue) {
            self.stmt_continue(kw).map(Statement::Continue).map(Some)
        } else if let Some(kw) = self.take(Token::Loop) {
            self.stmt_loop(kw).map(Statement::Loop).map(Some)
        } else if let Some(kw) = self.take(Token::Return) {
            self.stmt_return(kw).map(Statement::Return).map(Some)
        } else {
            Ok(None)
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_break(&mut self, _kw: Lexeme<'source>) -> Fallible<Break> {
        let label = self
            .take(Token::Identifier)
            .map(|ident| Identifier::new(ident.text));

        self.must_take(Token::Semicolon)?;
        Ok(Break { label })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_continue(&mut self, _kw: Lexeme<'source>) -> Fallible<Continue> {
        let label = self
            .take(Token::Identifier)
            .map(|ident| Identifier::new(ident.text));

        self.must_take(Token::Semicolon)?;
        Ok(Continue { label })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_loop(&mut self, _kw: Lexeme<'source>) -> Fallible<Loop> {
        let label = self
            .take(Token::Identifier)
            .map(|ident| Identifier::new(ident.text));

        let body = self.block()?;
        Ok(Loop { label, body })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn stmt_return(&mut self, _kw: Lexeme<'source>) -> Fallible<Return> {
        let expr = self.expression()?;
        self.must_take(Token::Semicolon)?;
        Ok(Return { expr })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn assign_or_expr(&mut self) -> Fallible<Either<Assignment, Expression>> {
        let expr = self.expression()?;

        if let Some(_eq) = self.take(Token::Equal) {
            let place =
                Place::try_from(expr).map_err(|err| self.error(ParseError::InvalidPlace(err)))?;

            let expr = self.expression()?;

            self.must_take(Token::Semicolon)?;

            return Ok(Either::L(Assignment { place, expr }));
        }

        Ok(Either::R(expr))
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ExprMode {
    All,
    NoObject,
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret, skip(self))]
    fn expression(&mut self) -> Fallible<Expression> {
        self.logic_or(ExprMode::All).map(Expression::LogicOr)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn expr_no_object(&mut self) -> Fallible<Expression> {
        self.logic_or(ExprMode::NoObject).map(Expression::LogicOr)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn logic_or(&mut self, mode: ExprMode) -> Fallible<LogicOr> {
        let first = self.logic_and(mode)?;

        let mut rest = Vec::new();
        while let Some(_or) = self.take(Token::Or) {
            let next = self.logic_and(mode)?;
            rest.push(next);
        }

        Ok(LogicOr { first, rest })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn logic_and(&mut self, mode: ExprMode) -> Fallible<LogicAnd> {
        let first = self.equality(mode)?;

        let mut rest = Vec::new();
        while let Some(_and) = self.take(Token::And) {
            let next = self.equality(mode)?;
            rest.push(next);
        }

        Ok(LogicAnd { first, rest })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn equality(&mut self, mode: ExprMode) -> Fallible<Equality> {
        let mut a = self.comparison(mode).map(Equality::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.comparison(mode)?;
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

    #[instrument(level = "trace", ret, skip(self))]
    fn comparison(&mut self, mode: ExprMode) -> Fallible<Comparison> {
        let mut a = self.term(mode).map(Comparison::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.term(mode)?;
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

    #[instrument(level = "trace", ret, skip(self))]
    fn term(&mut self, mode: ExprMode) -> Fallible<Term> {
        let mut a = self.factor(mode).map(Term::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.factor(mode)?;
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

    #[instrument(level = "trace", ret, skip(self))]
    fn factor(&mut self, mode: ExprMode) -> Fallible<Factor> {
        let mut a = self.unary(mode).map(Factor::Value)?;

        macro_rules! op {
            ($token:path, $op:path) => {
                if let Some(_lex) = self.take($token) {
                    let b = self.unary(mode)?;
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

    #[instrument(level = "trace", ret, skip(self))]
    fn unary(&mut self, mode: ExprMode) -> Fallible<Unary> {
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

        let mut a = self.call(mode).map(Unary::Value)?;
        while let Some(op) = ops.pop() {
            a = match op {
                Op::Neg => Unary::Neg(Box::new(a)),
                Op::Not => Unary::Not(Box::new(a)),
            };
        }
        Ok(a)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn call(&mut self, mode: ExprMode) -> Fallible<Call> {
        let mut callee = self.primary(mode).map(Call::Value)?;

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

    #[instrument(level = "trace", ret, skip(self))]
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

    #[instrument(level = "trace", ret, skip(self))]
    fn primary(&mut self, mode: ExprMode) -> Fallible<Primary> {
        if let Some(open) = self.take(Token::LeftBrace) {
            self.expr_block(open).map(Primary::Block)
        } else if let Some(if_) = self.take(Token::If) {
            self.expr_if(if_).map(Primary::If)
        } else if let Some(open) = self.take(Token::LeftParen) {
            self.expr_group(open).map(Box::new).map(Primary::Group)
        } else {
            self.atom(mode).map(Primary::Atom)
        }
    }
}

impl<'source> Parser<'source> {
    #[instrument(level = "trace", ret, skip(self))]
    fn atom(&mut self, mode: ExprMode) -> Fallible<Atom> {
        if let Some(ident) = self.take(Token::Self_) {
            let ident = Identifier::new(ident.text);
            return Ok(Atom::Identifier(ident));
        }

        if let Some(ident) = self.take(Token::Identifier) {
            let ident = Identifier::new(ident.text);

            // If this expression is allowed to end in an object literal, check for the opening
            // brace. Otherwise, let the brace be considered for some outer structure.
            //
            // This non-greedy option makes it possible to keep `if ident {` for simple
            // if-condition expressions while still allowing `if (obj{}) {` if someone really wants
            // that.
            //
            // TODO(let_chains_2): https://github.com/rust-lang/rust/issues/53667
            if mode == ExprMode::All {
                if let Some(open) = self.take(Token::LeftBrace) {
                    return self.expr_object(ident, open).map(Atom::Object);
                }
            }

            return Ok(Atom::Identifier(ident));
        }

        if let Some(open) = self.take(Token::LeftBracket) {
            let items = self.list_items(open)?;
            return Ok(Atom::List(List { items }));
        }

        self.literal().map(Atom::Literal)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn list_items(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<Expression>> {
        let mut args = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightBracket) {
                break;
            }

            let expr = self.expression()?;
            args.push(expr);

            if let Some(_sep) = self.take(Token::Comma) {
                continue;
            } else {
                self.must_take(Token::RightBracket)?;
                break;
            }
        }

        Ok(args)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn must_identifier(&mut self) -> Fallible<Identifier> {
        let ident = self.must_take(Token::Identifier)?;
        Ok(Identifier::new(ident.text))
    }

    #[instrument(level = "trace", ret, skip(self))]
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

    #[instrument(level = "trace", ret, skip(self))]
    fn expr_if(&mut self, _kw: Lexeme<'_>) -> Fallible<If> {
        // Even Rust resolves the parser ambiguity this way, so do the same for now!
        let condition = self.expr_no_object()?;
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

    #[instrument(level = "trace", ret, skip(self))]
    fn expr_group(&mut self, _open: Lexeme<'_>) -> Fallible<Expression> {
        let expr = self.expression()?;
        self.must_take(Token::RightParen)?;
        Ok(expr)
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn expr_object(&mut self, ty: Identifier, open: Lexeme<'_>) -> Fallible<Object> {
        let fields = self.object_fields(open)?;
        Ok(Object { ty, fields })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn object_fields(&mut self, _open: Lexeme<'_>) -> Fallible<Vec<(Identifier, Expression)>> {
        let mut fields = Vec::new();

        loop {
            if let Some(_close) = self.take(Token::RightBrace) {
                break;
            }

            let ident = self.must_identifier()?;

            self.must_take(Token::Equal)?;

            let expr = self.expression()?;
            fields.push((ident, expr));

            if let Some(_sep) = self.take(Token::Comma) {
                continue;
            } else {
                self.must_take(Token::RightBrace)?;
                break;
            }
        }

        Ok(fields)
    }

    #[instrument(level = "trace", ret, skip(self))]
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
            Err(self.error(ParseError::Other(msg)))
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn integer(&mut self, text: &str) -> Fallible<Literal> {
        text.parse::<BigInt>()
            .map(Literal::Integer)
            .map_err(|err| self.error(ParseError::ParseInt(err)))
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn float(&mut self, text: &str) -> Fallible<Literal> {
        text.parse::<f64>()
            .map(Literal::Float)
            .map_err(|err| self.error(ParseError::ParseFloat(err)))
    }
}

fn unescape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = peek_nth(s.chars());
    while let Some(c) = chars.next() {
        match c {
            '\\' => out.extend(unescape_sequence(&mut chars).into_iter()),
            c => out.push(c),
        };
    }
    out
}

fn unescape_sequence(chars: &mut PeekNth<Chars<'_>>) -> Vec<char> {
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
        'x' => match unescape_ascii(chars) {
            Some(a) => vec![a],
            None => vec!['\\', 'x'],
        },
        'u' => match unescape_unicode(chars) {
            Some(u) => vec![u],
            None => vec!['\\', 'u'],
        },

        // This was not a recognized escape sequence. Treat it as the literal text it was: a
        // backslash and whatever character came after.
        c => vec!['\\', c],
    }
}

fn unescape_ascii(chars: &mut PeekNth<Chars<'_>>) -> Option<char> {
    macro_rules! peek_digit {
        ($n:expr) => {{
            let Some(c) = chars.peek_nth($n) else {
                return None;
            };

            let Some(d) = c.to_digit(16) else {
                return None;
            };
            d
        }};
    }

    let hi = peek_digit!(0);
    let lo = peek_digit!(1);
    let unescaped = char::from_u32((hi << 4) | lo)?;

    chars.next().expect("peek 0");
    chars.next().expect("peek 1");
    Some(unescaped)
}

fn unescape_unicode(chars: &mut PeekNth<Chars<'_>>) -> Option<char> {
    macro_rules! peek_digit {
        ($n:expr) => {{
            let Some(c) = chars.peek_nth($n) else {
                return None;
            };

            let Some(d) = c.to_digit(16) else {
                return None;
            };
            d
        }};
    }

    macro_rules! peek {
        ($n:expr) => {{
            let Some(c) = chars.peek_nth($n) else {
                return None;
            };
            c
        }};
    }

    if peek!(0) != &'{' {
        return None;
    }

    let mut v = 0u32;
    let mut n = 1;

    loop {
        if peek!(n) == &'}' {
            break;
        }

        // If there wasn't a closing brace after `{` + 6 digits, this escape sequence is invalid.
        // Treat it as literal text and restart the unescaping process.
        if n > 1 + 6 {
            return None;
        }
        let d = peek_digit!(n);
        v = (v << 4) | d;
        n += 1;
    }

    if n == 1 {
        // This was an empty escape sequence, so ignore it.
        //
        //     \u{}
        //     __01
        //
        return None;
    }

    let unescaped = char::from_u32(v)?;

    // \u{abcdef}
    // __01234567
    //          n
    for _ in 0..=n {
        chars.next().expect("peek loop");
    }

    Some(unescaped)
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use rstest::rstest;

    use crate::testing::snapshot_name;

    use super::Parser;

    #[rstest]
    fn test_programs(
        #[files("test_programs/*.blis")]
        #[files("test_programs/err_compile/*.blis")]
        #[files("test_programs/err_runtime/*.blis")]
        path: PathBuf,
    ) {
        let source = std::fs::read_to_string(&path).unwrap();
        let ast = Parser::parse(&source).unwrap();

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(snapshot_name(&path, "ast"), ast);
        })
    }

    #[rstest]
    fn test_parse_errors(#[files("test_programs/err_parse/*.blis")] path: PathBuf) {
        let source = std::fs::read_to_string(&path).unwrap();
        let errors = Parser::parse(&source).unwrap_err();

        insta::with_settings!({
            input_file => &path,
            description => source,
            omit_expression => true,
        }, {
            insta::assert_ron_snapshot!(snapshot_name(&path, "errors"), errors);
        })
    }
}
