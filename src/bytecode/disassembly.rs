use num_rational::BigRational;
use serde::{Deserialize, Serialize};

use crate::bytecode::{Chunk, Constant, Func, Op};

#[derive(Clone, Serialize, Deserialize)]
pub struct DisassembledChunk {
    pub constants: Vec<DisassembledConstant>,
    pub globals: Vec<String>,
    pub code: Vec<Op>,
}

impl From<&Chunk> for DisassembledChunk {
    fn from(chunk: &Chunk) -> Self {
        let constants = chunk.constants.iter().map(Into::into).collect();
        let code: Result<Vec<_>, _> = chunk
            .iter_code()
            .map(|res| res.map(|(_pc, op)| op))
            .collect();

        Self {
            constants,
            code: code.unwrap(),
            globals: chunk.globals.clone(),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, strum::EnumIs, strum::EnumTryAs)]
pub enum DisassembledConstant {
    Rational(BigRational),
    Float(f64),
    String(String),
    Func(DisassembledFunc),
}

impl From<&Constant> for DisassembledConstant {
    fn from(constant: &Constant) -> Self {
        match constant {
            Constant::Rational(v) => Self::Rational(v.clone()),
            Constant::Float(v) => Self::Float(*v),
            Constant::String(v) => Self::String(v.clone()),
            Constant::Func(func) => Self::Func(func.into()),
        }
    }
}

#[derive(Clone, Serialize, Deserialize)]
pub struct DisassembledFunc {
    pub name: String,
    pub arity: u8,
    pub upvalues: u8,
    pub chunk: DisassembledChunk,
}

impl From<&Func> for DisassembledFunc {
    fn from(func: &Func) -> Self {
        Self {
            name: func.name.clone(),
            arity: func.arity,
            upvalues: func.upvalues,
            chunk: func.chunk.disassemble(),
        }
    }
}
