use std::sync::Arc;

use num_rational::BigRational;
use tracing::{debug, instrument, trace};

use crate::bytecode::{Chunk, Constant, Func, Op, OpError};
use crate::runtime::host;
use crate::runtime::{
    BoundMethod, Closure, HostFn, HostFunc, Instance, List, ObjPtr, Object, Runtime, RuntimeError,
    Type, Upvalue, Value, ValueType,
};

pub struct Vm<'fd> {
    opts: VmOptions<'fd>,
    frames: Vec<Frame>,
    runtime: Runtime,
}

pub struct VmOptions<'a> {
    pub stdout: Box<&'a mut dyn std::io::Write>,
    pub stderr: Box<&'a mut dyn std::io::Write>,
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

    #[error("type error: expected {} arguments, got {}", expected, actual)]
    Arity { expected: usize, actual: usize },

    #[error("index error: value `{}` cannot be indexed", value)]
    Index { value: Value },

    #[error("key error: value `{}` cannot be indexed by `{}`", value, key)]
    Key { value: Value, key: Value },
}

impl Vm<'_> {
    fn push(&mut self, value: Value) {
        self.runtime.push(value)
    }

    fn pop(&mut self) -> VmResult<Value> {
        self.runtime.pop().map_err(Into::into)
    }

    fn pop_n(&mut self, n: u8) -> VmResult<Vec<Value>> {
        let popped = self.runtime.pop_n(n as usize)?;
        let len = self.runtime.stack_len();

        for (i, value) in popped.iter().enumerate() {
            let slot = i + len;
            trace!({ ?slot, %value, }, "pop_n");
        }

        Ok(popped)
    }

    fn peek(&self, depth: usize) -> VmResult<&Value> {
        self.runtime.peek(depth).map_err(Into::into)
    }
}

impl Vm<'_> {
    fn call_value(&mut self, argc: u8) -> VmResult<()> {
        let callee = self.peek(argc as usize)?;
        let Some(ptr) = callee.try_as_object_ref() else {
            return Err(VmError::Type {
                expected: String::from("function"),
                actual: callee.clone(),
            });
        };

        match unsafe { ptr.as_ref() } {
            Object::HostFunc(f) => {
                let ret = {
                    let argv = self.runtime.argv(argc as usize);

                    (f.inner)(&mut self.opts, argc, argv)
                };

                // Replace the whole call frame (including the callee) with the return value.
                self.pop_n(argc + 1)?;
                self.push(ret);
                Ok(())
            }

            Object::Closure(closure) => {
                // TODO: unbound method arity?
                if argc != closure.func.arity {
                    return Err(VmError::Arity {
                        expected: closure.func.arity as usize,
                        actual: argc as usize,
                    });
                }

                // Subtract one extra slot so bp points to the caller itself.
                let bp = self.runtime.stack_offset(1 + argc as usize)?;
                self.frames.push(Frame { bp, pc: 0 });

                Ok(())
            }

            Object::BoundMethod(method) => {
                let method_argc = argc.checked_add(1).unwrap();

                // Replace the bound method with its real implementation.
                self.runtime
                    .replace(method_argc as usize, Value::Object(method.func))?;

                // Insert the receiver as the first argument.
                self.runtime.insert_as(argc as usize, method.recv.clone())?;
                self.call_value(method_argc)
            }

            _ => Err(VmError::Type {
                expected: String::from("function"),
                actual: callee.clone(),
            }),
        }
    }

    #[instrument(level = "trace", ret, skip(self))]
    fn capture_upvalue(&mut self, bp: usize, location: u8, index: u8) -> ObjPtr {
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

impl<'fd> Vm<'fd> {
    pub fn new(opts: VmOptions<'fd>) -> Self {
        let mut vm = Self {
            opts,
            frames: Vec::new(),
            runtime: Runtime::default(),
        };

        vm.define_host_func("print", host::print);
        vm.define_host_func("println", host::println);

        vm.define_host_type("object", vec![]);
        vm.define_host_type("List", vec![("append", host::list_append)]);

        vm
    }

    pub fn define_host_func(&mut self, name: &'static str, f: HostFn) {
        let name = String::from(name);

        let obj = Object::HostFunc(HostFunc {
            name: name.clone(),
            inner: Arc::new(f),
        });
        let ptr = self.runtime.alloc(obj);

        self.runtime.define_global(name, Value::Object(ptr));
    }

    pub fn define_host_type(&mut self, name: &'static str, methods: Vec<(&'static str, HostFn)>) {
        let ty_name = String::from(name);

        let ty = Object::Type(Type::new(ty_name.clone()));
        let ty_ptr = self.runtime.alloc(ty);

        self.runtime
            .define_global(ty_name.clone(), Value::Object(ty_ptr));

        for (name, method) in methods {
            let method_name = String::from(name);
            let method = Object::HostFunc(HostFunc {
                name: method_name.clone(),
                inner: Arc::new(method),
            });
            let method_ptr = self.runtime.alloc(method);

            let ty = unsafe { ty_ptr.as_mut() }.try_as_type_mut().unwrap();
            ty.set_method(method_name, Value::Object(method_ptr));
        }

        self.runtime.define_builtin(ty_name, Value::Object(ty_ptr));
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
        // TODO: Almost every `.unwrap()` in this function should be `.expect()` or Try.

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
            ($frame:expr) => {{
                let callee = self.runtime.stack_get($frame.bp); // Slot zero!
                let obj = callee.try_as_object_ref().unwrap();
                unsafe { obj.as_ref() }.try_as_closure_ref().unwrap()
            }};
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

            macro_rules! jump_forward {
                ($delta:expr) => {{
                    let pc = &mut frame!().pc;

                    // pc was already moved past this op. Put it back before jumping.
                    *pc = pc.checked_sub(op.size_bytes()).unwrap();

                    let delta = $delta;
                    *pc = pc.checked_add(delta as usize).unwrap();
                }};
            }

            macro_rules! jump_back {
                ($delta:expr) => {{
                    let pc = &mut frame!().pc;

                    // pc was already moved past this op. Put it back before jumping.
                    *pc = pc.checked_sub(op.size_bytes()).unwrap();

                    let delta = $delta;
                    *pc = pc.checked_sub(delta as usize).unwrap();
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
                            let b = self.pop().expect("peek").try_as_float().expect("peek");
                            let a = self.pop().expect("peek").try_as_float().expect("peek");
                            self.push(Value::Float($op_float(a, b)));
                        }

                        (Value::Rational(_), Value::Rational(_)) => {
                            let b = self.pop().expect("peek").try_as_rational().expect("peek");
                            let a = self.pop().expect("peek").try_as_rational().expect("peek");
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
                        Constant::Func(_) => {
                            panic!("funcs can't be stack values, this should have been Op::Closure")
                        }
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
                Op::List(len) => {
                    let items = self.pop_n(len)?;
                    let list = List::new(items);
                    let obj = self.runtime.alloc(Object::List(list));
                    self.push(Value::Object(obj));
                }
                Op::Object => {
                    let ty = self.pop()?;

                    let obj = Object::Instance(Instance::new(ty));
                    let ptr = self.runtime.alloc(obj);
                    self.push(Value::Object(ptr))
                }
                Op::Type(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let name = constant.try_as_string_ref().unwrap().clone();

                    let obj = Object::Type(Type::new(name));
                    let ptr = self.runtime.alloc(obj);
                    self.push(Value::Object(ptr))
                }

                Op::Jump(delta) => jump_forward!(delta),
                Op::JumpFalsePeek(delta) => {
                    if !self.peek(0)?.truthy() {
                        jump_forward!(delta);
                    }
                }
                Op::JumpFalsePop(delta) => {
                    if !self.pop()?.truthy() {
                        jump_forward!(delta);
                    }
                }
                Op::JumpTruePeek(delta) => {
                    if self.peek(0)?.truthy() {
                        jump_forward!(delta);
                    }
                }
                Op::JumpTruePop(delta) => {
                    if self.pop()?.truthy() {
                        jump_forward!(delta);
                    }
                }
                Op::Loop(delta) => jump_back!(delta),

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
                    let upvalue = unsafe { upvalue.as_ref() }.try_as_upvalue_ref().unwrap();

                    let value = match upvalue {
                        Upvalue::Stack(idx) => self.runtime.stack_get(*idx).clone(),
                        Upvalue::Heap(obj) => {
                            let boxed = unsafe { obj.as_ref() }.try_as_box_ref().unwrap();
                            unsafe { &**boxed }.clone()
                        }
                    };
                    self.push(value);
                }
                Op::SetUpvalue(idx) => {
                    let callee = callee!(frame!());
                    let value = self.peek(0).unwrap().clone();

                    let upvalue = callee.upvalues[idx as usize];
                    let upvalue = unsafe { upvalue.as_mut() }.try_as_upvalue_mut().unwrap();

                    match upvalue {
                        Upvalue::Stack(idx) => self.runtime.stack_put(*idx, value),
                        Upvalue::Heap(obj) => {
                            let boxed = unsafe { obj.as_ref() }.try_as_box_ref().unwrap();
                            unsafe { **boxed = value };
                        }
                    }
                }

                Op::DefineGlobal(idx) => {
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
                    let name = constant.try_as_string_ref().unwrap().clone();

                    let recv = self.pop()?.try_as_object().unwrap();

                    let v = match unsafe { recv.as_ref() } {
                        Object::Instance(i) => match i.get_field(&name) {
                            Some(value) => value.clone(),
                            None => {
                                let b = unsafe { Instance::get_method(recv, &name) };
                                let b = b.expect("type check");
                                Value::Object(self.runtime.alloc(b))
                            }
                        },

                        // TODO: Track the arity change for true methods
                        Object::Type(t) => t.get_method(&name).expect("type check").clone(),

                        Object::List(_) => {
                            let ty = self.runtime.get_builtin("List");
                            let ty = ty.try_as_object_ref().unwrap();
                            let ty = unsafe { ty.as_ref() }.try_as_type_ref().unwrap();

                            let method = ty.get_method(&name).expect("type check").clone();
                            let b = Object::BoundMethod(BoundMethod::new(recv, method));
                            Value::Object(self.runtime.alloc(b))
                        }

                        _ => todo!("type error"),
                    };

                    self.push(v);
                }
                Op::SetField(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let name = constant.try_as_string_ref().unwrap().clone();

                    let recv = *self.peek(1)?.try_as_object_ref().unwrap();

                    let value = self.pop()?;

                    let obj = unsafe { recv.as_mut() }.try_as_instance_mut().unwrap();
                    obj.set_field(name, value);
                }

                Op::GetMethod(idx) => {
                    // TODO: Is this ever used instead of GetField?
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let name = constant.try_as_string_ref().unwrap().clone();

                    let obj = self.pop()?.try_as_object().unwrap();
                    let ty = unsafe { obj.as_ref() }.try_as_type_ref().unwrap();

                    let v = ty.get_method(&name).unwrap().clone();
                    self.push(v);
                }
                Op::SetMethod(idx) => {
                    let chunk = chunk!(frame!());
                    let constant = &chunk.constants[idx as usize];
                    let name = constant.try_as_string_ref().unwrap().clone();

                    let method = self.pop()?;

                    let obj = self.peek(0)?.try_as_object_ref().unwrap();
                    let ty = unsafe { obj.as_mut() }.try_as_type_mut().unwrap();

                    ty.set_method(name, method);

                    // Leave the type on the stack to attach further methods.
                }

                Op::GetIndex => {
                    let key = self.pop()?;
                    let recv = self.pop()?.try_as_object().unwrap();

                    let v = match key {
                        Value::Rational(ref rat) if rat.is_integer() => {
                            let int = rat.numer();

                            match unsafe { recv.as_ref() } {
                                Object::List(l) => match l.get_item(int) {
                                    Some(v) => v,
                                    None => {
                                        return Err(VmError::Key {
                                            value: Value::Object(recv),
                                            key,
                                        });
                                    }
                                },

                                _ => todo!("type error"),
                            }
                        }
                        Value::String(name) => {
                            // Safety: There are two overlapping references to `recv` here, but
                            // they're both _immutable_.
                            match unsafe { recv.as_ref() } {
                                Object::Instance(i) => match i.get_field(&name) {
                                    Some(value) => value.clone(),
                                    None => {
                                        let b = unsafe { Instance::get_method(recv, &name) };
                                        let b = b.expect("type check");
                                        Value::Object(self.runtime.alloc(b))
                                    }
                                },

                                // TODO: Track the arity change for true methods
                                Object::Type(t) => t.get_method(&name).expect("type check").clone(),

                                _ => todo!("type error"),
                            }
                        }

                        Value::Nil
                        | Value::Boolean(_)
                        | Value::Float(_)
                        | Value::Rational(_)
                        | Value::Object(_) => todo!("custom index behavior?"),
                    };

                    self.push(v);
                }

                Op::SetIndex => {
                    let val = self.pop()?;
                    let key = self.pop()?;
                    let recv = self.pop()?.try_as_object().unwrap();

                    match key {
                        Value::Rational(ref rat) if rat.is_integer() => {
                            let idx = rat.numer();

                            match unsafe { recv.as_mut() } {
                                Object::List(l) => {
                                    l.set_item(idx, val).ok_or_else(|| VmError::Key {
                                        value: Value::Object(recv),
                                        key,
                                    })?;
                                }
                                _ => todo!("type error"),
                            }
                        }
                        Value::String(name) => match unsafe { recv.as_mut() } {
                            Object::Instance(i) => {
                                i.set_field((*name).clone(), val);
                            }

                            _ => todo!("type error"),
                        },

                        Value::Nil
                        | Value::Boolean(_)
                        | Value::Float(_)
                        | Value::Rational(_)
                        | Value::Object(_) => todo!("custom index behavior?"),
                    };
                }

                Op::Call(argc) => {
                    self.call_value(argc)?;
                }

                Op::Closure(idx) => {
                    let frame = frame!();
                    let chunk = chunk!(frame);
                    let bp = frame.bp;
                    let func = chunk.constants[idx as usize].try_as_func_ref().unwrap();

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
                            let b = self.pop().expect("peek").try_as_float().expect("peek");
                            let a = self.pop().expect("peek").try_as_float().expect("peek");
                            self.push(Value::Float(a + b));
                        }

                        (Value::Rational(_), Value::Rational(_)) => {
                            let b = self.pop().expect("peek").try_as_rational().expect("peek");
                            let a = self.pop().expect("peek").try_as_rational().expect("peek");
                            self.push(Value::Rational(a + b));
                        }

                        (Value::String(_), Value::String(_)) => {
                            let b = self.pop().expect("peek").try_as_string().expect("peek");
                            let a = self.pop().expect("peek").try_as_string().expect("peek");

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
