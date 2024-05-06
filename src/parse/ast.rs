use num_bigint::BigInt;

use crate::parse::Token;

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Type(Type),
    Func(Func),
    Let(Let),

    Statement(Statement),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Break(Break),
    Continue(Continue),
    Loop(Loop),

    Assignment(Assignment),
    Expression(Expression),
}

#[derive(Debug, Clone)]
pub enum Expression {
    LogicOr(LogicOr),
}

impl Expression {
    pub fn self_terminating(&self) -> bool {
        match self {
            Expression::LogicOr(or) => or.self_terminating(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct LogicOr {
    pub first: LogicAnd,
    pub rest: Vec<LogicAnd>,
}

impl LogicOr {
    pub fn self_terminating(&self) -> bool {
        self.rest.is_empty() && self.first.self_terminating()
    }
}

#[derive(Debug, Clone)]
pub struct LogicAnd {
    pub first: Equality,
    pub rest: Vec<Equality>,
}

impl LogicAnd {
    pub fn self_terminating(&self) -> bool {
        self.rest.is_empty() && self.first.self_terminating()
    }
}

#[derive(Debug, Clone)]
pub enum Equality {
    Value(Comparison),

    Eq(Box<Equality>, Comparison),
    Ne(Box<Equality>, Comparison),
}

impl Equality {
    pub fn self_terminating(&self) -> bool {
        match self {
            Equality::Value(comp) => comp.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Comparison {
    Value(Term),

    Ge(Box<Comparison>, Term),
    Gt(Box<Comparison>, Term),
    Le(Box<Comparison>, Term),
    Lt(Box<Comparison>, Term),
}

impl Comparison {
    pub fn self_terminating(&self) -> bool {
        match self {
            Comparison::Value(term) => term.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Term {
    Value(Factor),

    Add(Box<Term>, Factor),
    Sub(Box<Term>, Factor),
}

impl Term {
    pub fn self_terminating(&self) -> bool {
        match self {
            Term::Value(factor) => factor.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Factor {
    Value(Unary),

    Mul(Box<Factor>, Unary),
    Div(Box<Factor>, Unary),
    Rem(Box<Factor>, Unary),
}

impl Factor {
    pub fn self_terminating(&self) -> bool {
        match self {
            Factor::Value(unary) => unary.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Unary {
    Value(Call),

    Neg(Box<Unary>),
    Not(Box<Unary>),
}

impl Unary {
    pub fn self_terminating(&self) -> bool {
        match self {
            Unary::Value(call) => call.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Call {
    Value(Primary),

    Call(Box<Call>, Vec<Expression>),
    Index(Box<Call>, Box<Expression>),
    Field(Box<Call>, Identifier),
}

impl Call {
    pub fn self_terminating(&self) -> bool {
        match self {
            Call::Value(call) => call.self_terminating(),
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Primary {
    Block(Block),
    If(If),
    Group(Box<Expression>),
    Object(Object),

    Atom(Atom),
}

#[derive(Debug, Clone)]
pub struct Object {
    pub ty: Identifier,
    pub fields: Vec<(Identifier, Expression)>,
}

impl Primary {
    pub fn self_terminating(&self) -> bool {
        match self {
            Primary::Block(_) | Primary::If(_) | Primary::Object(_) => true,
            Primary::Atom(_) | Primary::Group(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub enum Atom {
    Identifier(Identifier),
    Literal(Literal),
    Object(Object),
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub place: Place,
    pub expr: Expression,
}

#[derive(Debug, Clone)]
pub enum Place {
    Field(Call, Identifier),
    Identifier(Identifier),
}

#[derive(thiserror::Error, Debug, Clone)]
#[error("cannot assign to `{:?}`, wanted {:?}", target, Token::Identifier)]
pub struct PlaceError {
    pub target: Expression,
}

impl TryFrom<Expression> for Place {
    type Error = PlaceError;

    fn try_from(expr: Expression) -> Result<Self, Self::Error> {
        let target = expr.clone();

        let Expression::LogicOr(expr) = expr;

        let LogicOr { first: expr, rest } = expr;
        if !rest.is_empty() {
            return Err(PlaceError { target });
        }

        let LogicAnd { first: expr, rest } = &expr;
        if !rest.is_empty() {
            return Err(PlaceError { target });
        }

        let Equality::Value(expr) = expr else {
            return Err(PlaceError { target });
        };

        let Comparison::Value(expr) = expr else {
            return Err(PlaceError { target });
        };

        let Term::Value(expr) = expr else {
            return Err(PlaceError { target });
        };

        let Factor::Value(expr) = expr else {
            return Err(PlaceError { target });
        };

        let Unary::Value(expr) = expr else {
            return Err(PlaceError { target });
        };

        if let Call::Value(expr) = expr {
            let Primary::Atom(expr) = expr else {
                return Err(PlaceError { target });
            };

            let Atom::Identifier(ident) = expr else {
                return Err(PlaceError { target });
            };

            Ok(Place::Identifier(ident.clone()))
        } else if let Call::Field(expr, ident) = expr {
            Ok(Place::Field(*expr.clone(), ident.clone()))
        } else {
            Err(PlaceError { target })
        }
    }
}

#[derive(Debug, Clone)]
pub struct Type {
    pub ident: Identifier,
    pub methods: Vec<Method>,
}

#[derive(Debug, Clone)]
pub struct Method {
    pub self_: bool,
    pub ident: Identifier,
    pub params: Vec<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct Func {
    pub ident: Identifier,
    pub params: Vec<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct Let {
    pub ident: Identifier,
    pub expr: Expression,
}

#[derive(Debug, Clone)]
pub struct Loop {
    pub label: Option<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone)]
pub struct Break {
    pub label: Option<Identifier>,
}

#[derive(Debug, Clone)]
pub struct Continue {
    pub label: Option<Identifier>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub decls: Vec<Declaration>,
    pub expr: Option<Box<Expression>>,
}

#[derive(Debug, Clone)]
pub struct If {
    pub condition: Box<Expression>,
    pub consequent: Block,
    pub alternative: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
    pub name: String,
}

impl Identifier {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }

    pub fn empty() -> Self {
        Self {
            name: String::from(""),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Nil,
    Boolean(bool),
    Integer(BigInt),
    Float(f64),
    String(String),
}
