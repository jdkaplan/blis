#[derive(Debug)]
pub enum Value {
    Nil,
    Boolean(bool),
    Integer(u64),
    Float(f64),
    String(String),
}

impl Value {
    pub fn truthy(&self) -> bool {
        match self {
            Value::Boolean(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }
}
