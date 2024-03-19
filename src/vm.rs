use crate::bytecode::{Chunk, Constant, Op, OpError};

#[derive(Debug)]
pub enum Value {
    Integer(u64),
    Float(f64),
    String(String),
}

impl From<Constant> for Value {
    fn from(constant: Constant) -> Self {
        match constant {
            Constant::Integer(v) => Value::Integer(v),
            Constant::Float(v) => Value::Float(v),
            Constant::String(v) => Value::String(v),
        }
    }
}

#[derive(Default)]
pub struct Vm {
    stack: Vec<Value>,
}

pub type VmResult<T> = Result<T, VmError>;

#[derive(thiserror::Error, Debug)]
#[error("vm error")]
pub enum VmError {
    Op(#[from] OpError),
}

impl Vm {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn interpret(&mut self, chunk: Chunk) -> VmResult<()> {
        let mut pc = 0;

        loop {
            let op = Op::scan(&chunk.code[pc..])?;
            let Some(op) = op else {
                return Ok(());
            };
            pc += op.size_bytes();

            match op {
                Op::Return => {
                    // TODO: Functions should actually return values
                    dbg!(self.stack.pop());
                }
                Op::Constant(idx) => {
                    let constant = &chunk.constants[idx as usize];
                    self.stack.push(Value::from(constant.clone()));
                }
            }
        }
    }
}
