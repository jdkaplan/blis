#[derive(Debug, Clone, strum::EnumDiscriminants)]
#[strum_discriminants(name(ValueType), derive(Hash, strum::EnumString, strum::Display))]
pub enum Value {
    Nil,
    Boolean(bool),
    Integer(u64),
    Float(f64),
    String(String), // TODO: Heap-allocate
}

impl Value {
    pub fn truthy(&self) -> bool {
        match self {
            Value::Boolean(b) => *b,
            Value::Nil => false,
            _ => true,
        }
    }

    pub fn is_a(&self, ty: ValueType) -> bool {
        ValueType::from(self) == ty
    }

    pub fn is_numeric(&self) -> bool {
        ValueType::from(self).is_numeric()
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        // Matching with (T, T) and (T, _) ensures that all cases are covered somewhat concisely
        // while also ensuring that Rust properly complains about unhandled cases.
        //
        // The (T, U) for different types will never be equal, but handling them with a default
        // case would cause bugs when I inevitably forget that this method needs to be updated
        // for new Value variants.
        match (self, other) {
            (Value::Nil, Value::Nil) => true,
            (Value::Nil, _) => false,

            (Value::Boolean(a), Value::Boolean(b)) => a == b,
            (Value::Boolean(_), _) => false,

            (Value::Integer(a), Value::Integer(b)) => a == b,
            (Value::Integer(_), _) => false,

            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Float(_), _) => false,

            (Value::String(a), Value::String(b)) => a == b,
            (Value::String(_), _) => false,
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        match (self, other) {
            (Value::Integer(a), Value::Integer(b)) => a.partial_cmp(b),
            (Value::Integer(_), _) => None,

            (Value::Float(a), Value::Float(b)) => a.partial_cmp(b),
            (Value::Float(_), _) => None,

            _ => unreachable!(),
        }
    }
}

impl ValueType {
    pub fn is_numeric(&self) -> bool {
        self == &ValueType::Integer || self == &ValueType::Float
    }
}
