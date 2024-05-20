use num_bigint::BigInt;
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
pub struct Program {
    pub decls: Vec<Declaration>,
}

#[derive(Debug, Clone, Serialize)]
pub enum Declaration {
    Type(Type),
    Func(Func),
    Let(Let),

    Statement(Statement),
}

#[derive(Debug, Clone, Serialize)]
pub enum Statement {
    Break(Break),
    Continue(Continue),
    Loop(Loop),
    Return(Return),

    Assignment(Assignment),
    Expression(Expression),
}

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
pub struct LogicOr {
    pub first: LogicAnd,
    pub rest: Vec<LogicAnd>,
}

impl LogicOr {
    pub fn self_terminating(&self) -> bool {
        self.rest.is_empty() && self.first.self_terminating()
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct LogicAnd {
    pub first: Equality,
    pub rest: Vec<Equality>,
}

impl LogicAnd {
    pub fn self_terminating(&self) -> bool {
        self.rest.is_empty() && self.first.self_terminating()
    }
}

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
pub enum Primary {
    Block(Block),
    If(If),
    Group(Box<Expression>),

    Atom(Atom),
}

#[derive(Debug, Clone, Serialize)]
pub struct Object {
    pub ty: Identifier,
    pub fields: Vec<(Identifier, Expression)>,
}

#[derive(Debug, Clone, Serialize)]
pub struct List {
    pub items: Vec<Expression>,
}

impl Primary {
    pub fn self_terminating(&self) -> bool {
        match self {
            Primary::Block(_) | Primary::If(_) => true,
            Primary::Atom(_) | Primary::Group(_) => false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub enum Atom {
    Identifier(Identifier),
    Literal(Literal),
    Object(Object),
    List(List),
}

#[derive(Debug, Clone, Serialize)]
pub struct Assignment {
    pub place: Place,
    pub expr: Expression,
}

#[derive(Debug, Clone, Serialize)]
pub enum Place {
    Field(Call, Identifier),
    Identifier(Identifier),
    Index(Call, Box<Expression>),
}

#[derive(thiserror::Error, Debug, Clone, Serialize)]
#[error("cannot assign to `{:?}`", target)]
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

        match expr {
            Call::Value(expr) => {
                let Primary::Atom(expr) = expr else {
                    return Err(PlaceError { target });
                };

                let Atom::Identifier(ident) = expr else {
                    return Err(PlaceError { target });
                };

                // Prevent assigning to `self` to avoid implying that the receiver can be changed
                // that way.
                if ident.name == "self" {
                    return Err(PlaceError { target });
                }

                Ok(Place::Identifier(ident.clone()))
            }
            Call::Field(obj, ident) => Ok(Place::Field(*obj.clone(), ident.clone())),
            Call::Index(obj, key) => Ok(Place::Index(*obj.clone(), key.clone())),
            Call::Call(_, _) => Err(PlaceError { target }),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct Type {
    pub ident: Identifier,
    pub methods: Vec<Method>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Method {
    pub self_: bool,
    pub ident: Identifier,
    pub params: Vec<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone, Serialize)]
pub struct Func {
    pub ident: Identifier,
    pub params: Vec<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone, Serialize)]
pub struct Let {
    pub ident: Identifier,
    pub expr: Expression,
}

#[derive(Debug, Clone, Serialize)]
pub struct Loop {
    pub label: Option<Identifier>,
    pub body: Block,
}

#[derive(Debug, Clone, Serialize)]
pub struct Return {
    pub expr: Expression,
}

#[derive(Debug, Clone, Serialize)]
pub struct Break {
    pub label: Option<Identifier>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Continue {
    pub label: Option<Identifier>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Block {
    pub decls: Vec<Declaration>,
    pub expr: Option<Box<Expression>>,
}

#[derive(Debug, Clone, Serialize)]
pub struct If {
    pub condition: Box<Expression>,
    pub consequent: Block,
    pub alternative: Option<Block>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
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

#[derive(Debug, Clone, Serialize)]
pub enum Literal {
    Nil,
    Boolean(bool),
    Integer(BigInt),
    Float(f64),
    String(String),
}
