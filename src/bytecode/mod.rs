use serde::{Deserialize, Serialize};

pub mod chunk;
pub mod op;

pub use chunk::{Chunk, Constant};
pub use op::{Op, OpError};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Func {
    pub name: String,
    pub arity: u8,
    pub chunk: Chunk,
}

impl PartialEq for Func {
    fn eq(&self, _other: &Self) -> bool {
        false
    }
}
