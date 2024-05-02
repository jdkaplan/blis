use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use num_rational::BigRational;
use tracing::{instrument, trace};

use crate::bytecode::{Chunk, Constant, Func, Op, OpError};
use crate::runtime::{Closure, HostFunc, RuntimeFn, Strings, Upvalue, Upvalues, Value, ValueType};

#[derive(Default)]
pub struct Vm {
    stack: Vec<Value>,
    globals: BTreeMap<String, Value>,
    frames: Vec<Frame>,
    upvalues: Upvalues,
    strings: Strings,
}

fn host_print(_argc: u8, argv: &[Value]) -> Value {
    if let Some(first) = argv.first() {
        print!("{}", first);
        for v in &argv[1..] {
            print!(" {}", v);
        }
    }

    println!();
    Value::Nil
}

struct Frame {
    bp: usize,
    pc: usize,
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
    Compare { a: Box<Value>, b: Box<Value> },

    #[error("type error: cannot perform arithmetic with `{:?}` and `{:?}`", a, b)]
    Arithmetic { a: Box<Value>, b: Box<Value> },
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

    fn pop_n(&mut self, n: u8) -> VmResult<()> {
        let n = n as usize;
        let len = self.stack.len();

        let new_len = len.checked_sub(n);
        let new_len = new_len.ok_or(VmError::NoValue { depth: n, len })?;

        for (slot, value) in self.stack[new_len..].iter().enumerate() {
            trace!({ ?slot, %value, }, "pop_n");
        }
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
    fn call_value(&mut self, argc: u8) -> VmResult<()> {
        let callee = self.peek(argc as usize)?;

        match callee {
            Value::HostFunc(f) => {
                let ret = {
                    let start = self.stack.len() - argc as usize;
                    let argv = &self.stack[start..];

                    (f.inner)(argc, argv)
                };

                // Replace the whole call frame (including the callee) with the return value.
                self.pop_n(argc + 1)?;
                self.push(ret);
                Ok(())
            }
            Value::Closure(closure) => {
                if argc != closure.func.arity {
                    todo!("arity mismatch");
                }
                let argc: usize = argc.into();

                // Subtract one extra slot so bp points to the caller itself.
                let bp = self.stack.len().checked_sub(1 + argc).unwrap();
                self.frames.push(Frame { bp, pc: 0 });

                Ok(())
            }
            actual => Err(VmError::Type {
                expected: String::from("function"),
                actual: actual.clone(),
            }),
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn capture_upvalue(&mut self, bp: usize, location: u8, index: u8) -> Arc<Mutex<Upvalue>> {
        match location {
            1 => {
                let slot = bp + index as usize;

                self.upvalues.capture(slot)
            }
            0 => {
                // This points to wherever the _parent's_ upvalue does.
                let Value::Closure(enclosing) = &self.stack[bp] else {
                    unreachable!()
                };
                enclosing.upvalues[index as usize].clone()
            }
            other => panic!("invalid upvalue location: {:?}", other),
        }
    }

    #[instrument(level = "trace", skip(self))]
    fn close_upvalues(&mut self, len: usize) {
        self.upvalues.close(&self.stack, len);
    }
}

impl Vm {
    pub fn new() -> Self {
        let mut vm = Self::default();
        vm.set_host_func("print", host_print);
        vm
    }

    pub fn set_host_func(&mut self, name: &'static str, f: RuntimeFn) {
        let name = String::from(name);

        let hosted = Value::HostFunc(HostFunc {
            name: name.clone(),
            inner: Arc::new(f),
        });
        self.globals.insert(name, hosted);
    }

    pub fn interpret(&mut self, chunk: Chunk) -> VmResult<()> {
        let func = Func {
            name: String::from(""),
            arity: 0,
            upvalues: 0,
            chunk,
        };

        let script = Value::Closure(Closure {
            func: Arc::new(func),
            upvalues: vec![],
        });

        self.push(script);
        self.call_value(0)?;

        self.run()
    }

    fn run(&mut self) -> VmResult<()> {
        macro_rules! frame {
            () => {
                self.frames.last_mut().expect("non-empty call stack")
            };
        }

        macro_rules! chunk {
            ($frame:expr) => {
                &callee!($frame).func.chunk
            };
        }

        macro_rules! callee {
            ($frame:expr) => {
                match &self.stack[$frame.bp] {
                    Value::Closure(closure) => closure,
                    _ => unreachable!(),
                }
            };
        }

        loop {
            let op = {
                let frame = frame!();
                let chunk = chunk!(frame);

                for (slot, value) in self.stack.iter().enumerate() {
                    trace!({ ?slot, %value }, "stack");
                }

                let pc = &mut frame.pc;
                let bp = frame.bp;
                trace!({ ?pc, ?bp }, "fetch");

                let op = Op::scan(&chunk.code[*pc..])?;
                let Some(op) = op else {
                    return Ok(());
                };
                *pc += op.size_bytes();
                op
            };

            trace!({ ?op }, "execute");

            macro_rules! jump {
                ($delta:expr) => {{
                    let pc = &mut frame!().pc;

                    // pc was already moved past this op. Put it back before jumping.
                    *pc = pc.checked_sub(op.size_bytes()).unwrap();

                    let delta = $delta;
                    if delta.is_negative() {
                        *pc = pc.checked_sub((-delta) as usize).unwrap();
                    } else {
                        *pc = pc.checked_add(delta as usize).unwrap();
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
                            a: Box::new(a.clone()),
                            b: Box::new(b.clone()),
                        });
                    }

                    let b = self.pop()?;
                    let a = self.pop()?;
                    self.push(Value::Boolean($op(&a, &b)));
                }};
            }

            macro_rules! bin_op {
                ($op_rat:expr, $op_float:expr) => {{
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

                        (Value::Rational(_), Value::Rational(_)) => {
                            let Ok(Value::Rational(b)) = self.pop() else {
                                unreachable!()
                            };
                            let Ok(Value::Rational(a)) = self.pop() else {
                                unreachable!()
                            };
                            self.push(Value::Rational($op_rat(a, b)));
                        }

                        (a, b) => {
                            return Err(VmError::Arithmetic {
                                a: Box::new(a.clone()),
                                b: Box::new(b.clone()),
                            });
                        }
                    }
                }};
            }

            match op {
                Op::Return => {
                    let value = self.pop()?;

                    // Stack locations at bp or above are about to disappear. Close any open
                    // upvalues that point to them.
                    let bp = frame!().bp;
                    self.close_upvalues(bp);

                    let frame = self.frames.pop().expect("non-empty call stack");
                    if self.frames.is_empty() {
                        // Pop `main` itself to leave the value stack empty.
                        self.pop()?;
                        assert!(self.stack.is_empty());
                        return Ok(());
                    }

                    // Pop any local state from the returning function.
                    self.stack.truncate(frame.bp);

                    trace!({ ?value }, "returning");
                    self.push(value);
                }

                Op::Pop => {
                    let v = self.pop()?;
                    trace!({ ?v }, "pop");
                }
                Op::PopN(n) => {
                    // These n stack locations are about to disappear. Close any open upvalues that
                    // point to them.
                    let len = self.stack.len() - n as usize;
                    self.close_upvalues(len);

                    self.pop_n(n)?;
                }

                Op::PopUnderN(n) => {
                    // Save the block's expression value to push back on.
                    let v = self.pop()?;

                    // These n stack locations are about to disappear. Close any open upvalues that
                    // point to them.
                    let len = self.stack.len() - n as usize;
                    self.close_upvalues(len);

                    self.pop_n(n)?;
                    self.push(v);
                }

                Op::Constant(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];

                    let v = match constant {
                        Constant::Rational(v) => Value::Rational(v.clone()),
                        Constant::Float(v) => Value::Float(*v),
                        Constant::String(v) => {
                            let ptr = self.strings.intern_ref(v);
                            Value::String(ptr)
                        }
                        Constant::Func(_) => unreachable!(),
                    };

                    self.push(v);
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

                Op::GetLocal(slot) => {
                    let bp = frame!().bp;
                    let value = self.stack[bp + slot as usize].clone();
                    self.push(value);
                }
                Op::SetLocal(slot) => {
                    let bp = frame!().bp;
                    let value = self.pop()?;
                    self.stack[bp + slot as usize] = value;
                }

                Op::GetUpvalue(idx) => {
                    let callee = callee!(frame!());
                    let upvalue = &callee.upvalues[idx as usize];

                    let value = {
                        let upvalue = upvalue.lock().unwrap();
                        match &*upvalue {
                            Upvalue::Stack(slot) => self.stack[*slot].clone(),
                            Upvalue::Heap(mu) => mu.lock().unwrap().clone(),
                        }
                    };
                    self.push(value);
                }
                Op::SetUpvalue(idx) => {
                    let callee = callee!(frame!());
                    let value = self.peek(0).unwrap().clone();

                    let upvalue = callee.upvalues[idx as usize].clone();

                    let mut upvalue = upvalue.lock().unwrap();
                    match &mut *upvalue {
                        Upvalue::Stack(slot) => self.stack[*slot] = value,
                        Upvalue::Heap(mu) => {
                            let mut v = mu.lock().unwrap();
                            *v = value;
                        }
                    }
                }

                Op::GlobalDefine(idx) => {
                    let chunk = chunk!(frame!());
                    let global = chunk.globals[idx as usize].clone();
                    let value = self.pop()?;
                    self.globals.insert(global, value);
                }
                Op::GetGlobal(idx) => {
                    let chunk = chunk!(frame!());
                    let global = chunk.globals[idx as usize].clone();

                    let Some(value) = self.globals.get(&global) else {
                        return Err(VmError::UndefinedGlobal { name: global });
                    };
                    self.push(value.clone());
                }
                Op::SetGlobal(idx) => {
                    let chunk = chunk!(frame!());
                    let global = chunk.globals[idx as usize].clone();

                    let value = self.pop()?;

                    let Some(dest) = self.globals.get_mut(&global) else {
                        return Err(VmError::UndefinedGlobal { name: global });
                    };

                    *dest = value;
                }

                Op::Call(argc) => {
                    self.call_value(argc)?;
                }
                Op::Index => todo!(),
                Op::Closure(idx) => {
                    let frame = frame!();
                    let chunk = chunk!(frame);
                    let bp = frame.bp;
                    let constant = &chunk.constants[idx as usize];
                    let Constant::Func(func) = constant else {
                        unreachable!()
                    };

                    let mut closure = Closure {
                        func: Arc::new(func.clone()),
                        upvalues: Vec::with_capacity(func.upvalues as usize),
                    };

                    // This instruction is variable-length. There are two additional bytes for each
                    // upvalue.
                    //
                    // Temporarily copy the program counter to avoid borrow checker issues on
                    // `frame`.
                    let mut pc = frame.pc;
                    let chunk = chunk.clone();
                    for _ in 0..func.upvalues {
                        let location = chunk.code[pc];
                        pc += 1;

                        let index = chunk.code[pc];
                        pc += 1;

                        let ptr = self.capture_upvalue(bp, location, index);
                        closure.upvalues.push(ptr);
                    }
                    assert_eq!(closure.func.upvalues as usize, closure.upvalues.len());

                    // And now put the new pc back where it belongs (after all the upvalue data).
                    frame!().pc = pc;

                    self.push(Value::Closure(closure));
                }

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
                        Value::Rational(i) => {
                            let val = Value::Rational(-i);
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
                Op::Add => {
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
                            self.push(Value::Float(a + b));
                        }

                        (Value::Rational(_), Value::Rational(_)) => {
                            let Ok(Value::Rational(b)) = self.pop() else {
                                unreachable!()
                            };
                            let Ok(Value::Rational(a)) = self.pop() else {
                                unreachable!()
                            };
                            self.push(Value::Rational(a + b));
                        }

                        (Value::String(_), Value::String(_)) => {
                            let Ok(Value::String(b)) = self.pop() else {
                                unreachable!()
                            };
                            let Ok(Value::String(a)) = self.pop() else {
                                unreachable!()
                            };
                            let c = self.strings.concatenate(a, b);
                            self.push(Value::String(c));
                        }

                        (a, b) => {
                            return Err(VmError::Arithmetic {
                                a: Box::new(a.clone()),
                                b: Box::new(b.clone()),
                            });
                        }
                    }
                }
                Op::Sub => bin_op!(std::ops::Sub::<BigRational>::sub, std::ops::Sub::<f64>::sub),
                Op::Mul => bin_op!(std::ops::Mul::<BigRational>::mul, std::ops::Mul::<f64>::mul),
                Op::Div => bin_op!(std::ops::Div::<BigRational>::div, std::ops::Div::<f64>::div),
                Op::Rem => bin_op!(std::ops::Rem::<BigRational>::rem, std::ops::Rem::<f64>::rem),
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
