use crate::parse::Token;

#[derive(Debug, Clone)]
pub struct Program {
    pub decls: Vec<Declaration>,
}

#[derive(Debug, Clone)]
pub enum Declaration {
    Let(Let),

    Statement(Statement),
}

#[derive(Debug, Clone)]
pub enum Statement {
    Assignment(Assignment),

    Expression(Expression),
}

#[derive(Debug, Clone)]
pub enum Expression {
    Block(Block),
    If(If),

    // TODO: Atom?
    Identifier(Identifier),
    Literal(Literal),
}

impl Expression {
    pub fn self_terminating(&self) -> bool {
        match self {
            Expression::Block(_) | Expression::If(_) => true,
            Expression::Identifier(_) | Expression::Literal(_) => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub place: Place,
    pub expr: Expression,
}

#[derive(Debug, Clone)]
pub enum Place {
    Identifier(Identifier),
}

#[derive(thiserror::Error, Debug, Clone)]
#[error("cannot assign to `{:?}`, wanted {:?}", target, Token::Identifier)]
pub struct PlaceError {
    pub target: Expression,
}

impl TryFrom<Expression> for Place {
    type Error = PlaceError;

    fn try_from(target: Expression) -> Result<Self, Self::Error> {
        match target {
            Expression::Identifier(ident) => Ok(Place::Identifier(ident)),
            target => Err(PlaceError { target }),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Let {
    pub ident: Identifier,
    pub expr: Expression,
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

#[derive(Debug, Clone)]
pub struct Identifier {
    pub name: String,
}

impl Identifier {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Nil,
    Boolean(bool),
    Integer(u64),
    Float(f64),
    String(String),
}
