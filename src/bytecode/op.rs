#[derive(
    Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, strum::Display, strum::FromRepr,
)]
#[repr(u8)]
pub enum Op {
    Return = 0x00,
    Pop = 0x01,
    PopN(u8) = 0x02,
    PopUnderN(u8) = 0x03,

    Constant(u8) = 0x04,
    Nil = 0x05,
    False = 0x06,
    True = 0x07,
    Object = 0x08,

    Call(u8) = 0x10,
    Index = 0x11,
    Closure(u8) = 0x12,

    GetLocal(u8) = 0x20,
    SetLocal(u8) = 0x21,
    GetUpvalue(u8) = 0x22,
    SetUpvalue(u8) = 0x23,
    GlobalDefine(u8) = 0x26,
    GetGlobal(u8) = 0x27,
    SetGlobal(u8) = 0x28,
    GetField(u8) = 0x29,
    SetField(u8) = 0x2a,

    Not = 0x30,
    Eq = 0x31,
    Ne = 0x32,
    Gt = 0x33,
    Ge = 0x34,
    Lt = 0x35,
    Le = 0x36,

    Neg = 0x37,
    Add = 0x38,
    Sub = 0x39,
    Mul = 0x3a,
    Div = 0x3b,
    Rem = 0x3c,

    // Jumps
    Jump(i16) = 0x60,
    JumpFalsePeek(i16) = 0x61,
    JumpFalsePop(i16) = 0x62,
    JumpTruePeek(i16) = 0x63,
    JumpTruePop(i16) = 0x64,
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
            Op::Return
            | Op::Pop
            | Op::Nil
            | Op::False
            | Op::True
            | Op::Object
            | Op::Index
            | Op::Not
            | Op::Eq
            | Op::Ne
            | Op::Gt
            | Op::Ge
            | Op::Lt
            | Op::Le
            | Op::Neg
            | Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Rem => {}

            Op::Constant(ref mut byte)
            | Op::PopN(ref mut byte)
            | Op::PopUnderN(ref mut byte)
            | Op::Call(ref mut byte)
            | Op::Closure(ref mut byte)
            | Op::GetLocal(ref mut byte)
            | Op::SetLocal(ref mut byte)
            | Op::GetUpvalue(ref mut byte)
            | Op::SetUpvalue(ref mut byte)
            | Op::GlobalDefine(ref mut byte)
            | Op::GetGlobal(ref mut byte)
            | Op::SetGlobal(ref mut byte)
            | Op::GetField(ref mut byte)
            | Op::SetField(ref mut byte) => {
                *byte = *code.get(1).ok_or(OpError::MissingByte { op, b: 1 })?;
            }

            Op::Jump(ref mut int)
            | Op::JumpFalsePeek(ref mut int)
            | Op::JumpFalsePop(ref mut int)
            | Op::JumpTruePeek(ref mut int)
            | Op::JumpTruePop(ref mut int) => {
                let hi = code.get(1).ok_or(OpError::MissingByte { op, b: 1 })?;
                let lo = code.get(2).ok_or(OpError::MissingByte { op, b: 2 })?;
                *int = i16::from_be_bytes([*hi, *lo]);
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
            Op::Return
            | Op::Pop
            | Op::Nil
            | Op::False
            | Op::True
            | Op::Object
            | Op::Index
            | Op::Not
            | Op::Eq
            | Op::Ne
            | Op::Gt
            | Op::Ge
            | Op::Lt
            | Op::Le
            | Op::Neg
            | Op::Add
            | Op::Sub
            | Op::Mul
            | Op::Div
            | Op::Rem => {}

            Op::Constant(byte)
            | Op::PopN(byte)
            | Op::PopUnderN(byte)
            | Op::Call(byte)
            | Op::Closure(byte)
            | Op::GetLocal(byte)
            | Op::SetLocal(byte)
            | Op::GetUpvalue(byte)
            | Op::SetUpvalue(byte)
            | Op::GlobalDefine(byte)
            | Op::GetGlobal(byte)
            | Op::SetGlobal(byte)
            | Op::GetField(byte)
            | Op::SetField(byte) => {
                bytes.push(*byte);
            }

            Op::Jump(int)
            | Op::JumpFalsePeek(int)
            | Op::JumpFalsePop(int)
            | Op::JumpTruePeek(int)
            | Op::JumpTruePop(int) => {
                bytes.extend(int.to_be_bytes());
            }
        }

        bytes
    }
}
