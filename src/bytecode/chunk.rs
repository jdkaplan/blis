use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, PartialEq, Serialize, Deserialize)]
pub enum Constant {
    Integer(u64),
    Float(f64),
}

#[derive(Serialize, Deserialize)]
pub struct Chunk {
    pub constants: Vec<Constant>,
    pub code: Vec<u8>,
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
