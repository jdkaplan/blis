pub struct Program {
    pub decls: Vec<Declaration>,
}

pub enum Declaration {
    Statement(Statement),
}

pub enum Statement {
    Expression(Expression),
}

pub enum Expression {
    Literal(Literal),
}

pub enum Literal {
    Nil,
    Boolean(bool),
    Integer(u64),
    Float(f64),
    String(String),
}
