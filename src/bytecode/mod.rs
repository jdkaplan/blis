use serde::{Deserialize, Serialize};

pub mod chunk;
pub mod disassembly;
pub mod op;

pub use chunk::{Chunk, Constant};
pub use op::{Capture, Op, OpError};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Func {
    pub name: String,
    pub arity: u8,
    pub upvalues: u8,
    pub chunk: Chunk,
}
