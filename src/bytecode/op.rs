#[derive(
    Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, strum::Display, strum::FromRepr,
)]
#[repr(u8)]
pub enum Op {
    Return = 0x00,

    Constant(u8) = 0x10,
}

#[derive(thiserror::Error, Debug)]
pub enum OpError {
    #[error("unknown opcode: {:x}", opcode)]
    UnknownOpcode { opcode: u8 },

    #[error("missing byte for op: {:?}, byte {}", op, b)]
    MissingByte { op: Op, b: usize },
}

impl Op {
    pub fn scan(code: &[u8]) -> Result<Option<Self>, OpError> {
        let Some(&opcode) = code.first() else {
            return Ok(None);
        };

        let op = Self::from_repr(opcode).ok_or(OpError::UnknownOpcode { opcode })?;

        let mut build = op;
        match build {
            Op::Return => {}

            Op::Constant(ref mut byte) => {
                *byte = *code.get(1).ok_or(OpError::MissingByte { op, b: 1 })?;
            }
        }

        Ok(Some(build))
    }

    pub fn size_bytes(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        // Safety: This is the recommended way in The Book for getting the discriminant value
        // when the enums hold values.
        //
        // https://doc.rust-lang.org/reference/items/enumerations.html#pointer-casting
        let opcode = unsafe { *(self as *const Self as *const u8) };

        let mut bytes = vec![opcode];

        match self {
            Op::Return => {}

            Op::Constant(byte) => {
                bytes.push(*byte);
            }
        }

        bytes
    }
}
