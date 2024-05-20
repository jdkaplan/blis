use std::io;

use num_rational::BigRational;
use serde::{Deserialize, Serialize};

use crate::bytecode::disassembly::DisassembledChunk;
use crate::bytecode::{Func, Op, OpError};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, strum::EnumIs, strum::EnumTryAs)]
pub enum Constant {
    Rational(BigRational),
    Float(f64),
    String(String),
    Func(Func),
}

#[derive(Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct Chunk {
    pub constants: Vec<Constant>,
    pub globals: Vec<String>,
    pub code: Vec<u8>,
}

impl std::fmt::Debug for Chunk {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Chunk")
            .field("constants", &format!("(count: {})", self.constants.len()))
            .field("globals", &format!("(count: {})", self.globals.len()))
            .field("code", &format!("(bytes: {})", self.code.len()))
            .finish()
    }
}

// Code
impl Chunk {
    pub fn push(&mut self, op: Op) {
        self.push_bytes(&op.to_bytes())
    }

    pub fn push_bytes(&mut self, bytes: &[u8]) {
        self.code.extend(bytes)
    }

    pub fn add_constant(&mut self, constant: Constant) -> u8 {
        // Reuse existing constants when possible.
        if let Some(idx) = self.find_constant(&constant) {
            return idx;
        }

        let idx = self.constants.len();
        assert!(idx < u8::MAX.into());

        self.constants.push(constant);
        idx as u8
    }

    fn find_constant(&self, constant: &Constant) -> Option<u8> {
        // TODO: HashMap/BTreeMap?
        self.constants
            .iter()
            .position(|c| c == constant)
            .map(|idx| idx.try_into().expect("add_constant enforces count"))
    }
}

// Globals
impl Chunk {
    pub fn define_global(&mut self, name: String) {
        let id = self.make_global(name);
        self.push(Op::DefineGlobal(id));
    }

    fn find_global(&self, name: &str) -> Option<u8> {
        // TODO: HashMap/BTreeMap?
        self.globals
            .iter()
            .position(|g| g == name)
            .map(|idx| idx.try_into().expect("make_global enforces count"))
    }

    pub fn make_global(&mut self, name: String) -> u8 {
        if let Some(id) = self.find_global(&name) {
            return id;
        }

        let idx = self.globals.len();
        let idx: u8 = idx
            .try_into()
            .expect("less than 256 constants, needs GlobalDefine2?");

        self.globals.push(name);
        idx
    }
}

#[must_use]
#[derive(Debug, Copy, Clone)]
pub struct PendingJump(usize);

// Jumps
impl Chunk {
    #[must_use = "set_jump_target"]
    pub fn prepare_jump(&mut self, op: Op) -> PendingJump {
        let idx = self.code.len();
        self.push(op);
        PendingJump(idx)
    }

    pub fn set_jump_target(&mut self, jump: PendingJump) {
        let idx = jump.0;
        let target = self.code.len();

        let offset: u16 = target
            .checked_sub(idx)
            .expect("jump is always backwards")
            .try_into()
            .expect("jump offset fits in two bytes");

        let [hi, lo] = offset.to_be_bytes();
        self.code[idx + 1] = hi;
        self.code[idx + 2] = lo;
    }
}

#[derive(thiserror::Error, Debug)]
pub enum ChunkReadError {
    #[error(transparent)]
    Deserialize(postcard::Error),

    #[error("extra bytes at end of file: {0:?}")]
    ExtraBytes(Vec<u8>),
}

#[derive(thiserror::Error, Debug)]
pub enum ChunkWriteError {
    #[error(transparent)]
    Serialize(postcard::Error),
}

// Compiled files
impl Chunk {
    pub fn read(r: impl io::Read) -> Result<Self, ChunkReadError> {
        let mut extra_bytes = Vec::new();

        let (chunk, (_, _)) =
            postcard::from_io((r, &mut extra_bytes)).map_err(ChunkReadError::Deserialize)?;

        if extra_bytes.is_empty() {
            Ok(chunk)
        } else {
            Err(ChunkReadError::ExtraBytes(extra_bytes))
        }
    }

    pub fn write(&self, w: impl io::Write) -> Result<(), ChunkWriteError> {
        postcard::to_io(self, w).map_err(ChunkWriteError::Serialize)?;
        Ok(())
    }
}

impl Chunk {
    pub fn iter_code(&self) -> CodeIterator<'_> {
        CodeIterator {
            code: &self.code,
            pc: 0,
            errored: false,
        }
    }
}

pub struct CodeIterator<'a> {
    code: &'a [u8],
    pc: usize,
    errored: bool,
}

impl Iterator for CodeIterator<'_> {
    type Item = Result<(usize, Op), OpError>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.errored {
            return None;
        }

        let pc = self.pc;
        match Op::scan(&self.code[pc..]) {
            Ok(None) => None,

            Ok(Some(op)) => {
                self.pc += op.size_bytes();
                Some(Ok((pc, op)))
            }

            Err(err) => {
                self.errored = true;
                Some(Err(err))
            }
        }
    }
}

impl Chunk {
    pub fn disassemble(&self) -> DisassembledChunk {
        self.into()
    }
}
