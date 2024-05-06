use std::fmt;

use num_rational::BigRational;

use crate::runtime::{HostFunc, InternedString, Object};

#[derive(Debug, Clone, strum::EnumDiscriminants)]
#[strum_discriminants(name(ValueType), derive(Hash, strum::EnumString, strum::Display))]
pub enum Value {
    Nil,
    Boolean(bool),
    Float(f64),
    Rational(BigRational),
    String(InternedString),
    HostFunc(HostFunc),
    Object(*mut Object),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Nil => write!(f, "nil"),
            Value::Boolean(v) => write!(f, "{}", if *v { "true" } else { "false" }),
            Value::Float(v) => write!(f, "{}", v),
            Value::Rational(v) => write!(f, "{}", v),
            Value::String(v) => write!(f, "{}", v),
            Value::HostFunc(v) => write!(f, "<func {:?}>", v.name),
            Value::Object(ptr) => {
                let obj = unsafe { &**ptr };
                write!(f, "<{} {:?}>", obj, ptr)
            }
        }
    }
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

            (Value::Float(a), Value::Float(b)) => a == b,
            (Value::Float(_), _) => false,

            (Value::Rational(a), Value::Rational(b)) => a == b,
            (Value::Rational(_), _) => false,

            (Value::String(a), Value::String(b)) => a == b,
            (Value::String(_), _) => false,

            // Functions are never equal to anything. In theory, they could be equal to themselves,
            // but getting clear rules for identity there doesn't feel worth it.
            //
            // TODO: Should Object equality apply to host functions?
            (Value::HostFunc(_), Value::HostFunc(_)) => false,
            (Value::HostFunc(_), _) => false,

            (Value::Object(a), Value::Object(b)) => a == b,
            (Value::Object(_), _) => false,
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;

        // TODO: Maybe Erlang's "type ordering is arbitrary but there _is_ one" is better?
        match (self, other) {
            (Value::Nil, Value::Nil) => Some(Ordering::Equal),
            (Value::Nil, _) => None,

            (Value::Boolean(a), Value::Boolean(b)) => a.partial_cmp(b),
            (Value::Boolean(_), _) => None,

            (Value::Float(a), Value::Float(b)) => a.partial_cmp(b),
            (Value::Float(_), _) => None,

            (Value::Rational(a), Value::Rational(b)) => a.partial_cmp(b),
            (Value::Rational(_), _) => None,

            (Value::String(a), Value::String(b)) => a.partial_cmp(b),
            (Value::String(_), _) => None,

            // Functions aren't comparable to each other nor to values of other types.
            (Value::HostFunc(_), Value::HostFunc(_)) => None,
            (Value::HostFunc(_), _) => None,

            // Objects have no default ordering.
            (Value::Object(_), Value::Object(_)) => None,
            (Value::Object(_), _) => None,
        }
    }
}

impl ValueType {
    pub fn is_numeric(&self) -> bool {
        self == &ValueType::Rational || self == &ValueType::Float
    }
}
