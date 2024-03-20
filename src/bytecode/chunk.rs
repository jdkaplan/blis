use serde::{Deserialize, Serialize};

use crate::bytecode::Op;

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constant {
    Integer(u64),
    Float(f64),
    String(String),
}

#[derive(Default, Serialize, Deserialize)]
pub struct Chunk {
    pub constants: Vec<Constant>,
    pub code: Vec<u8>,
}

impl Chunk {
    pub fn push(&mut self, op: Op) {
        self.code.extend(op.to_bytes())
    }

    pub fn add_constant(&mut self, constant: Constant) -> u8 {
        let idx = self.constants.len();
        assert!(idx < u8::MAX.into());

        self.constants.push(constant);
        idx as u8
    }
}

#[must_use]
#[derive(Debug)]
pub struct PendingJump(usize);

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

        let offset: i16 = (target - idx)
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

impl Chunk {
    pub fn read(r: impl std::io::Read) -> Result<Self, ChunkReadError> {
        let mut extra_bytes = Vec::new();

        let (chunk, (_, _)) =
            postcard::from_io((r, &mut extra_bytes)).map_err(ChunkReadError::Deserialize)?;

        if extra_bytes.is_empty() {
            Ok(chunk)
        } else {
            Err(ChunkReadError::ExtraBytes(extra_bytes))
        }
    }

    pub fn write(&self, w: impl std::io::Write) -> Result<(), ChunkWriteError> {
        postcard::to_io(self, w).map_err(ChunkWriteError::Serialize)?;
        Ok(())
    }
}
