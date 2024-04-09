pub mod chunk;
pub mod op;

pub use chunk::{Chunk, Constant};
pub use op::{Op, OpError};

#[derive(Debug, Clone)]
pub struct Func {
    pub name: String,
    pub arity: u8,
    pub chunk: Chunk,
}
