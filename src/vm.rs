use std::sync::Arc;

use num_rational::BigRational;
use tracing::{debug, instrument, trace};

use crate::bytecode::{Chunk, Constant, Func, Op, OpError};
use crate::runtime::{
    Closure, HostFunc, Instance, Object, Runtime, RuntimeError, RuntimeFn, Upvalue, Value,
    ValueType,
};

#[derive(Default)]
pub struct Vm {
    frames: Vec<Frame>,
    runtime: Runtime,
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

    #[error(transparent)]
    Runtime(#[from] RuntimeError),

    #[error("type error: expected `{}`, got `{:?}`", expected, actual)]
    Type { expected: String, actual: Value },

    #[error("type error: cannot compare `{:?}` and `{:?}`", a, b)]
    Compare { a: Box<Value>, b: Box<Value> },

    #[error("type error: cannot perform arithmetic with `{:?}` and `{:?}`", a, b)]
    Arithmetic { a: Box<Value>, b: Box<Value> },
}

impl Vm {
    fn push(&mut self, value: Value) {
        self.runtime.push(value)
    }

    fn pop(&mut self) -> VmResult<Value> {
        self.runtime.pop().map_err(Into::into)
    }

    fn pop_n(&mut self, n: u8) -> VmResult<()> {
        let popped = self.runtime.pop_n(n as usize)?;

        for (slot, value) in popped {
            trace!({ ?slot, %value, }, "pop_n");
        }

        Ok(())
    }

    fn peek(&self, depth: usize) -> VmResult<&Value> {
        self.runtime.peek(depth).map_err(Into::into)
    }
}

impl Vm {
    fn call_value(&mut self, argc: u8) -> VmResult<()> {
        let callee = self.peek(argc as usize)?;

        match callee {
            Value::HostFunc(f) => {
                let ret = {
                    let argv = self.runtime.argv(argc as usize);

                    (f.inner)(argc, argv)
                };

                // Replace the whole call frame (including the callee) with the return value.
                self.pop_n(argc + 1)?;
                self.push(ret);
                return Ok(());
            }
            Value::Object(obj) => {
                let obj = unsafe { &**obj };

                if let Object::Closure(closure) = obj {
                    if argc != closure.func.arity {
                        todo!("arity mismatch");
                    }

                    // Subtract one extra slot so bp points to the caller itself.
                    let bp = self.runtime.stack_offset(1 + argc as usize)?;
                    self.frames.push(Frame { bp, pc: 0 });

                    return Ok(());
                }
            }
            _ => {} // fall through
        }

        Err(VmError::Type {
            expected: String::from("function"),
            actual: callee.clone(),
        })
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn capture_upvalue(&mut self, bp: usize, location: u8, index: u8) -> *mut Object {
        match location {
            1 => {
                let slot = bp + index as usize;
                self.runtime.capture_local(slot)
            }
            0 => {
                // This points to wherever the _parent's_ upvalue does.
                self.runtime.recapture_upvalue(bp, index as usize)
            }
            other => panic!("invalid upvalue location: {:?}", other),
        }
    }

    #[instrument(level = "trace", skip(self))]
    fn close_upvalues(&mut self, len: usize) {
        self.runtime.close_upvalues(len)
    }
}

impl Vm {
    pub fn new() -> Self {
        let mut vm = Self::default();
        vm.define_host_func("print", host_print);
        vm
    }

    pub fn define_host_func(&mut self, name: &'static str, f: RuntimeFn) {
        let name = String::from(name);

        let hosted = Value::HostFunc(HostFunc {
            name: name.clone(),
            inner: Arc::new(f),
        });
        self.runtime.define_global(name, hosted);
    }

    pub fn interpret(&mut self, chunk: Chunk) -> VmResult<()> {
        let func = Func {
            name: String::from(""),
            arity: 0,
            upvalues: 0,
            chunk,
        };

        let script = Object::Closure(Closure {
            func: Arc::new(func),
            upvalues: vec![],
        });

        let ptr = self.runtime.alloc(script);

        self.push(Value::Object(ptr));
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
                match self.runtime.stack_get($frame.bp) {
                    Value::Object(obj) => unsafe { &**obj }.as_closure(),
                    _ => unreachable!(),
                }
            };
        }

        loop {
            self.runtime.trace_stack();

            let op = {
                let frame = frame!();
                let chunk = chunk!(frame);

                let pc = &mut frame.pc;
                let bp = frame.bp;
                debug!({ ?pc, ?bp }, "fetch");

                let op = Op::scan(&chunk.code[*pc..])?;
                let Some(op) = op else {
                    return Ok(());
                };
                *pc += op.size_bytes();
                op
            };

            debug!({ ?op }, "execute");

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
                    let frame = self.frames.pop().expect("non-empty call stack");

                    // Stack locations at bp or after are about to disappear. Close any open
                    // upvalues that point to them.
                    self.close_upvalues(frame.bp);

                    // This is the return value that will be pushed back on after popping the
                    // call frame.
                    let value = self.pop()?;

                    // Pop any local state from the returning function.
                    self.runtime.pop_frame(frame.bp);

                    trace!({ ?value }, "returning");
                    self.push(value);

                    // If this is the top-level script's return, exit instead.
                    if self.frames.is_empty() {
                        self.pop()?;
                        assert!(self.runtime.stack_empty());
                        return Ok(());
                    }
                }

                Op::Pop => {
                    // No need to close upvalues here. This instruction is only used to pop
                    // intermediate values that cannot be captured (since they don't have names).

                    let v = self.pop()?;
                    trace!({ ?v }, "pop");
                }
                Op::PopN(n) => {
                    // These n stack locations are about to disappear. Close any open upvalues that
                    // point to them.
                    let len = self.runtime.stack_offset(n as usize)?;
                    self.close_upvalues(len);

                    self.pop_n(n)?;
                }

                Op::PopUnderN(n) => {
                    // These n stack locations underneath the block expression value are about to
                    // disappear. Close any open upvalues that point to them.
                    //
                    // GC: The value itself must stay on the stack to make sure it's reachable as
                    // a root.
                    let start = self.runtime.stack_offset(1 + n as usize)?;
                    let end = self.runtime.stack_offset(0)?;
                    self.runtime.close_upvalues_range(start..end);

                    // Save the block's expression value to push back on.
                    let v = self.pop()?;

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
                            let ptr = self.runtime.intern(v);
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
                Op::Object => {
                    let obj = Object::Instance(Instance {
                        ty: Value::Nil,
                        fields: Default::default(),
                    });
                    let ptr = self.runtime.alloc(obj);
                    self.push(Value::Object(ptr))
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
                    let idx = bp + slot as usize;

                    let value = self.runtime.stack_get(idx).clone();
                    self.push(value);
                }
                Op::SetLocal(slot) => {
                    let bp = frame!().bp;
                    let idx = bp + slot as usize;

                    let value = self.pop()?;
                    self.runtime.stack_put(idx, value);
                }

                Op::GetUpvalue(idx) => {
                    let callee = callee!(frame!());

                    let upvalue = callee.upvalues[idx as usize];
                    let upvalue = unsafe { &*upvalue }.as_upvalue();

                    let value = match upvalue {
                        Upvalue::Stack(idx) => self.runtime.stack_get(*idx).clone(),
                        Upvalue::Heap(obj) => {
                            let boxed = unsafe { &**obj }.as_box();
                            let v = unsafe { &**boxed };
                            v.clone()
                        }
                    };
                    self.push(value);
                }
                Op::SetUpvalue(idx) => {
                    let callee = callee!(frame!());
                    let value = self.peek(0).unwrap().clone();

                    let upvalue = callee.upvalues[idx as usize];
                    let upvalue = unsafe { &mut *upvalue }.as_upvalue_mut();

                    match upvalue {
                        Upvalue::Stack(idx) => self.runtime.stack_put(*idx, value),
                        Upvalue::Heap(obj) => {
                            let boxed = unsafe { &**obj }.as_box();
                            unsafe { **boxed = value };
                        }
                    }
                }

                Op::GlobalDefine(idx) => {
                    let chunk = chunk!(frame!());
                    let name = chunk.globals[idx as usize].clone();
                    let value = self.pop()?;
                    self.runtime.define_global(name, value);
                }
                Op::GetGlobal(idx) => {
                    let chunk = chunk!(frame!());
                    let name = &chunk.globals[idx as usize];
                    let value = self.runtime.get_global(name)?;
                    self.push(value.clone());
                }
                Op::SetGlobal(idx) => {
                    let chunk = chunk!(frame!());
                    let name = chunk.globals[idx as usize].clone();

                    let value = self.pop()?;
                    self.runtime.set_global(name, value)?;
                }

                Op::GetField(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let Constant::String(name) = constant else {
                        unreachable!()
                    };
                    let name = name.clone();

                    let Value::Object(ptr) = self.pop()? else {
                        todo!("type error");
                    };

                    let obj = unsafe { &*ptr }.as_instance();
                    let v = obj.get_field(&name).unwrap().clone();
                    self.push(v);
                }
                Op::SetField(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let Constant::String(name) = constant else {
                        unreachable!()
                    };
                    let name = name.clone();

                    let Value::Object(ptr) = self.peek(1)? else {
                        todo!("type error");
                    };
                    let ptr = *ptr;

                    let value = self.pop()?;

                    let obj = unsafe { &mut *ptr }.as_instance_mut();
                    obj.set_field(name, value);
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

                    let obj = Object::Closure(closure);
                    let ptr = self.runtime.alloc(obj);
                    self.push(Value::Object(ptr));
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
                            let c = self.runtime.concatenate(a, b);
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
