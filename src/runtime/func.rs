use std::sync::Arc;

use crate::bytecode::Func;
use crate::runtime::{Gc, ObjPtr, Trace, Value};

pub type RuntimeFn = fn(argc: u8, argv: &[Value]) -> Value;

#[derive(Debug, Clone)]
pub struct HostFunc {
    pub name: String,
    pub inner: Arc<RuntimeFn>,
}

impl Trace for HostFunc {
    fn trace(&self, _gc: &mut Gc) {
        // No references
    }
}

#[derive(Debug, Clone)]
pub struct Closure {
    pub func: Arc<Func>,
    pub upvalues: Vec<ObjPtr>, // Object::Upvalue(_)
}

impl Trace for Closure {
    fn trace(&self, gc: &mut Gc) {
        for v in &self.upvalues {
            assert!(unsafe { v.as_ref() }.is_upvalue(), "{:?}", v);
            gc.mark_object(*v);
        }
    }
}

#[derive(Debug, Clone)]
pub struct BoundMethod {
    pub recv: Value,
    pub func: Value,
}

impl Trace for BoundMethod {
    fn trace(&self, gc: &mut Gc) {
        gc.mark_value(&self.recv);
        gc.mark_value(&self.func);
    }
}

impl BoundMethod {
    pub fn new(recv: ObjPtr, func: Value) -> Self {
        Self {
            recv: Value::Object(recv),
            func,
        }
    }
}
