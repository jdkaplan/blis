use crate::bytecode::{Chunk, Constant, Op, OpError};
use crate::runtime::Value;

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
    fn pop(&mut self) -> VmResult<Value> {
        self.stack.pop().ok_or(VmError::NoValue {
            depth: 0,
            len: self.stack.len(),
        })
    }

    fn pop_n(&mut self, n: usize) -> VmResult<()> {
        let len = self.stack.len();

        let new_len = len.checked_sub(n);
        let new_len = new_len.ok_or(VmError::NoValue { depth: n, len })?;

        dbg!(&self.stack[new_len..]);
        self.stack.truncate(new_len);
        Ok(())
    }

    fn peek(&mut self, depth: usize) -> VmResult<&Value> {
        self.stack.rget(depth).ok_or(VmError::NoValue {
            depth,
            len: self.stack.len(),
        })
    }
}

impl Vm {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn interpret(&mut self, chunk: Chunk) -> VmResult<()> {
        let mut pc = 0;

        loop {
            let op = Op::scan(&chunk.code[pc..])?;
            dbg!(op);
            let Some(op) = op else {
                return Ok(());
            };
            pc += op.size_bytes();

            macro_rules! jump {
                ($delta:expr) => {{
                    // pc was already moved past this op. Put it back before jumping.
                    pc = pc.checked_sub(op.size_bytes()).unwrap();

                    let delta = $delta;
                    if delta.is_negative() {
                        pc = pc
                            .checked_sub((delta as isize).try_into().unwrap())
                            .unwrap();
                    } else {
                        pc = pc.checked_add(delta as usize).unwrap();
                    }
                }};
            }

            match op {
                Op::Return => {
                    dbg!(&self.stack);
                    return Ok(());
                }

                Op::Pop => {
                    dbg!(self.pop()?);
                }
                Op::PopN(n) => {
                    self.pop_n(n as usize)?;
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

                Op::Jump(delta) => jump!(delta),
                Op::JumpFalsePeek(delta) => {
                    if !self.peek(0)?.truthy() {
                        jump!(delta);
                    }
                }
                Op::JumpFalsePop(delta) => {
                    if !self.pop()?.truthy() {
                        jump!(delta);
                    }
                }
                Op::JumpTruePeek(delta) => {
                    if self.peek(0)?.truthy() {
                        jump!(delta);
                    }
                }
                Op::JumpTruePop(delta) => {
                    if self.pop()?.truthy() {
                        jump!(delta);
                    }
                }
            }
        }
    }
}

trait VecExt<T> {
    fn rget(&self, index: usize) -> Option<&T>;
}

impl<T> VecExt<T> for Vec<T> {
    fn rget(&self, index: usize) -> Option<&T> {
        self.get(self.len() - 1 - index)
    }
}
