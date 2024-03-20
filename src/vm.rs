use crate::bytecode::{Chunk, Constant, Op, OpError};

#[derive(Debug)]
pub enum Value {
    Nil,
    Boolean(bool),
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
pub enum VmError {
    #[error(transparent)]
    Op(#[from] OpError),

    #[error(
        "stack error: expected value at depth {}, but stack length was {}",
        depth,
        len
    )]
    NoValue { depth: usize, len: usize },
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
                    dbg!(&self.stack);
                    return Ok(());
                }

                Op::Pop => {
                    dbg!(self.stack.pop());
                }
                Op::PopN(n) => {
                    let n = n as usize;
                    let len = self.stack.len();

                    let new_len = len.checked_sub(n);
                    let new_len = new_len.ok_or(VmError::NoValue { depth: n, len })?;

                    dbg!(&self.stack[new_len..]);
                    self.stack.truncate(new_len);
                }

                Op::Constant(idx) => {
                    let constant = &chunk.constants[idx as usize];
                    self.stack.push(Value::from(constant.clone()));
                }

                Op::Nil => {
                    self.stack.push(Value::Nil);
                }
                Op::False => {
                    self.stack.push(Value::Boolean(false));
                }
                Op::True => {
                    self.stack.push(Value::Boolean(true));
                }
            }
        }
    }
}
