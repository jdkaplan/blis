use std::collections::BTreeMap;

use tracing::trace;

use crate::bytecode::{Chunk, Constant, Op, OpError};
use crate::runtime::{Value, ValueType};

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
    globals: BTreeMap<String, Value>,
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

    #[error("name error: global variable `{}` was not defined", name)]
    UndefinedGlobal { name: String },

    #[error("type error: expected `{}`, got `{:?}`", expected, actual)]
    Type { expected: String, actual: Value },

    #[error("type error: cannot compare `{:?}` and `{:?}`", a, b)]
    Compare { a: Value, b: Value },

    #[error("type error: cannot perform arithmetic with `{:?}` and `{:?}`", a, b)]
    Arithmetic { a: Value, b: Value },
}

impl Vm {
    fn push(&mut self, value: Value) {
        self.stack.push(value)
    }

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

        trace!({ suffix =? self.stack[new_len..] }, "pop_n");
        self.stack.truncate(new_len);
        Ok(())
    }

    fn peek(&self, depth: usize) -> VmResult<&Value> {
        self.stack.rget(depth).ok_or(VmError::NoValue {
            depth,
            len: self.stack.len(),
        })
    }
}

impl Vm {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            globals: BTreeMap::new(),
        }
    }

    pub fn interpret(&mut self, chunk: Chunk) -> VmResult<()> {
        let mut pc = 0;

        loop {
            trace!({ ?pc, ?self.stack }, "fetch");

            let op = Op::scan(&chunk.code[pc..])?;
            let Some(op) = op else {
                return Ok(());
            };
            pc += op.size_bytes();

            trace!({ ?op }, "execute");

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

            macro_rules! cmp_op {
                ($op:expr) => {{
                    let b = self.peek(0)?;
                    let a = self.peek(1)?;

                    let a_ty = ValueType::from(a);
                    let b_ty = ValueType::from(b);

                    if a_ty != b_ty || !a_ty.is_numeric() {
                        return Err(VmError::Compare {
                            a: a.clone(),
                            b: b.clone(),
                        });
                    }

                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.push(Value::Boolean($op(&a, &b)));
                }};
            }

            macro_rules! bin_op {
                ($op_int:expr, $op_float:expr) => {{
                    let b = self.peek(0)?;
                    let a = self.peek(1)?;

                    match (a, b) {
                        (Value::Float(_), Value::Float(_)) => {
                            let Ok(Value::Float(b)) = self.pop() else {
                                unreachable!()
                            };
                            let Ok(Value::Float(a)) = self.pop() else {
                                unreachable!()
                            };
                            self.push(Value::Float($op_float(a, b)));
                        }

                        (Value::Integer(_), Value::Integer(_)) => {
                            let Ok(Value::Integer(b)) = self.pop() else {
                                unreachable!()
                            };
                            let Ok(Value::Integer(a)) = self.pop() else {
                                unreachable!()
                            };
                            self.push(Value::Integer($op_int(a, b)));
                        }

                        (a, b) => {
                            return Err(VmError::Arithmetic {
                                a: a.clone(),
                                b: b.clone(),
                            });
                        }
                    }
                }};
            }

            match op {
                Op::Return => {
                    trace!({ ?self.stack }, "returning");
                    return Ok(());
                }

                Op::Pop => {
                    let v = self.pop()?;
                    trace!({ ?v }, "pop");
                }
                Op::PopN(n) => {
                    self.pop_n(n as usize)?;
                }

                Op::Constant(idx) => {
                    let constant = &chunk.constants[idx as usize];
                    self.push(Value::from(constant.clone()));
                }

                Op::Nil => {
                    self.push(Value::Nil);
                }
                Op::False => {
                    self.push(Value::Boolean(false));
                }
                Op::True => {
                    self.push(Value::Boolean(true));
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

                Op::LocalGet(slot) => {
                    let value = self.stack[slot as usize].clone();
                    self.push(value);
                }
                Op::LocalSet(slot) => {
                    let value = self.pop()?;
                    self.stack[slot as usize] = value;
                }

                Op::GlobalDefine(idx) => {
                    let global = chunk.globals[idx as usize].clone();
                    let value = self.pop()?;
                    self.globals.insert(global, value);
                }
                Op::GlobalGet(idx) => {
                    let global = chunk.globals[idx as usize].clone();

                    let Some(value) = self.globals.get(&global) else {
                        return Err(VmError::UndefinedGlobal { name: global });
                    };
                    self.push(value.clone());
                }
                Op::GlobalSet(idx) => {
                    let global = chunk.globals[idx as usize].clone();

                    let value = self.pop()?;

                    let Some(dest) = self.globals.get_mut(&global) else {
                        return Err(VmError::UndefinedGlobal { name: global });
                    };

                    *dest = value;
                }

                Op::Call(_) => todo!(),
                Op::Index => todo!(),

                Op::Not => {
                    let a = self.pop()?;
                    self.push(Value::Boolean(!a.truthy()));
                }

                Op::Eq => {
                    self.peek(0)?;
                    self.peek(1)?;

                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.push(Value::Boolean(a == b))
                }
                Op::Ne => {
                    self.peek(0)?;
                    self.peek(1)?;

                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.push(Value::Boolean(a != b))
                }

                Op::Lt => cmp_op!(PartialOrd::lt),
                Op::Le => cmp_op!(PartialOrd::le),
                Op::Gt => cmp_op!(PartialOrd::gt),
                Op::Ge => cmp_op!(PartialOrd::ge),

                Op::Neg => {
                    let a = self.peek(0)?;

                    match a {
                        Value::Integer(i) => {
                            let val = Value::Integer(i.wrapping_neg());
                            let _ = self.pop().expect("peek");
                            self.push(val);
                        }
                        Value::Float(f) => {
                            let val = Value::Float(-f);
                            let _ = self.pop().expect("peek");
                            self.push(val);
                        }
                        other => {
                            return Err(VmError::Type {
                                expected: String::from("number (integer or float)"),
                                actual: other.clone(),
                            });
                        }
                    }
                }
                // TODO: String concatenation
                Op::Add => bin_op!(std::ops::Add::<u64>::add, std::ops::Add::<f64>::add),
                Op::Sub => bin_op!(std::ops::Sub::<u64>::sub, std::ops::Sub::<f64>::sub),
                Op::Mul => bin_op!(std::ops::Mul::<u64>::mul, std::ops::Mul::<f64>::mul),
                Op::Div => bin_op!(std::ops::Div::<u64>::div, std::ops::Div::<f64>::div),
                Op::Rem => bin_op!(std::ops::Rem::<u64>::rem, std::ops::Rem::<f64>::rem),
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
