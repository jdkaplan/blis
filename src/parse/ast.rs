pub struct Program {
    pub decls: Vec<Declaration>,
}

pub enum Declaration {
    Statement(Statement),
}

pub enum Statement {
    Expression(Expression),
}

pub struct Block {
    pub decls: Vec<Declaration>,
    pub expr: Option<Box<Expression>>,
}

pub enum Expression {
    Block(Block),
    If(If),
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

pub struct If {
    pub condition: Box<Expression>,
    pub consequent: Block,
    pub alternative: Option<Block>,
}

#[derive(Debug, Clone)]
pub struct Identifier {
    pub name: String,
}

pub enum Literal {
    Nil,
    Boolean(bool),
    Integer(u64),
    Float(f64),
    String(String),
}
