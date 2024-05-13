use serde::{Deserialize, Serialize};

// TODO: Document stack effects to help test the compiler.
#[derive(
    Debug,
    Clone,
    PartialEq,
    Eq,
    PartialOrd,
    Ord,
    Hash,
    Serialize,
    Deserialize,
    strum::Display,
    strum::FromRepr,
    strum::EnumDiscriminants,
)]
#[strum_discriminants(name(Opcode), derive(Hash, strum::EnumString, strum::Display))]
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
    List(u8) = 0x08,
    Object = 0x09,
    Type(u8) = 0x0a,

    Call(u8) = 0x10,
    Closure(u8, u8, Vec<Capture>) = 0x11,

    GetLocal(u8) = 0x20,
    SetLocal(u8) = 0x21,
    GetUpvalue(u8) = 0x22,
    SetUpvalue(u8) = 0x23,
    DefineGlobal(u8) = 0x26,
    GetGlobal(u8) = 0x27,
    SetGlobal(u8) = 0x28,
    GetField(u8) = 0x29,
    SetField(u8) = 0x2a,
    GetMethod(u8) = 0x2b,
    SetMethod(u8) = 0x2c,
    GetIndex = 0x2d,
    SetIndex = 0x2e,

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
    Jump(u16) = 0x60,
    JumpFalsePeek(u16) = 0x61,
    JumpFalsePop(u16) = 0x62,
    JumpTruePeek(u16) = 0x63,
    JumpTruePop(u16) = 0x64,
    Loop(u16) = 0x65,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum Capture {
    Local(u8),
    Nonlocal(u8),
}

#[derive(thiserror::Error, Debug)]
pub enum OpError {
    #[error("unknown opcode: {:x}", opcode)]
    UnknownOpcode { opcode: u8 },

    #[error("missing byte for op: {:?}, byte {}", opcode, offset)]
    MissingByte { opcode: Opcode, offset: usize },
}

trait SliceExt {
    fn get_byte(&self, offset: usize, opcode: Opcode) -> Result<u8, OpError>;
}

impl SliceExt for [u8] {
    fn get_byte(&self, offset: usize, opcode: Opcode) -> Result<u8, OpError> {
        self.get(offset)
            .copied()
            .ok_or(OpError::MissingByte { opcode, offset })
    }
}

impl Op {
    pub fn scan(code: &[u8]) -> Result<Option<Self>, OpError> {
        let Some(&opcode) = code.first() else {
            return Ok(None);
        };

        let op = Self::from_repr(opcode).ok_or(OpError::UnknownOpcode { opcode })?;
        let opcode: Opcode = op.clone().into();

        let mut build = op;
        match build {
            Op::Return
            | Op::Pop
            | Op::Nil
            | Op::False
            | Op::True
            | Op::Object
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
            | Op::Rem
            | Op::GetIndex
            | Op::SetIndex => {}

            Op::Constant(ref mut byte)
            | Op::PopN(ref mut byte)
            | Op::PopUnderN(ref mut byte)
            | Op::List(ref mut byte)
            | Op::Type(ref mut byte)
            | Op::Call(ref mut byte)
            | Op::GetLocal(ref mut byte)
            | Op::SetLocal(ref mut byte)
            | Op::GetUpvalue(ref mut byte)
            | Op::SetUpvalue(ref mut byte)
            | Op::DefineGlobal(ref mut byte)
            | Op::GetGlobal(ref mut byte)
            | Op::SetGlobal(ref mut byte)
            | Op::GetField(ref mut byte)
            | Op::SetField(ref mut byte)
            | Op::GetMethod(ref mut byte)
            | Op::SetMethod(ref mut byte) => {
                *byte = code.get_byte(1, opcode)?;
            }

            Op::Jump(ref mut int)
            | Op::JumpFalsePeek(ref mut int)
            | Op::JumpFalsePop(ref mut int)
            | Op::JumpTruePeek(ref mut int)
            | Op::JumpTruePop(ref mut int)
            | Op::Loop(ref mut int) => {
                let hi = code.get_byte(1, opcode)?;
                let lo = code.get_byte(2, opcode)?;
                *int = u16::from_be_bytes([hi, lo]);
            }

            Op::Closure(ref mut constant_id, ref mut upvalue_count, ref mut captures) => {
                *constant_id = code.get_byte(1, opcode)?;
                *upvalue_count = code.get_byte(2, opcode)?;

                let mut b = 3;
                for _ in 0..(*upvalue_count) {
                    let loc = code.get_byte(b, opcode)?;
                    b += 1;

                    let idx = code.get_byte(b, opcode)?;
                    b += 1;

                    captures.push(match loc {
                        1 => Capture::Local(idx),
                        0 => Capture::Nonlocal(idx),
                        other => panic!("invalid upvalue location: {:?}", other),
                    })
                }
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
            | Op::Rem
            | Op::GetIndex
            | Op::SetIndex => {}

            Op::Constant(byte)
            | Op::PopN(byte)
            | Op::PopUnderN(byte)
            | Op::List(byte)
            | Op::Type(byte)
            | Op::Call(byte)
            | Op::GetLocal(byte)
            | Op::SetLocal(byte)
            | Op::GetUpvalue(byte)
            | Op::SetUpvalue(byte)
            | Op::DefineGlobal(byte)
            | Op::GetGlobal(byte)
            | Op::SetGlobal(byte)
            | Op::GetField(byte)
            | Op::SetField(byte)
            | Op::GetMethod(byte)
            | Op::SetMethod(byte) => {
                bytes.push(*byte);
            }

            Op::Jump(int)
            | Op::JumpFalsePeek(int)
            | Op::JumpFalsePop(int)
            | Op::JumpTruePeek(int)
            | Op::JumpTruePop(int)
            | Op::Loop(int) => {
                bytes.extend(int.to_be_bytes());
            }

            Op::Closure(constant_id, upvalue_count, upvalues) => {
                bytes.push(*constant_id);
                bytes.push(*upvalue_count);
                for upvalue in upvalues {
                    match upvalue {
                        Capture::Local(idx) => {
                            bytes.push(1);
                            bytes.push(*idx);
                        }
                        Capture::Nonlocal(idx) => {
                            bytes.push(0);
                            bytes.push(*idx);
                        }
                    }
                }
            }
        }

        bytes
    }
}
