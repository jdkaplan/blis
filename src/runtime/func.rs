use std::sync::Arc;

use crate::bytecode::Func;
use crate::runtime::{Gc, HostFn, ObjPtr, Object, Trace, Value};

#[derive(Debug, Clone)]
pub struct HostFunc {
    pub name: String,
    pub inner: Arc<HostFn>,
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
    pub func: ObjPtr,
}

impl Trace for BoundMethod {
    fn trace(&self, gc: &mut Gc) {
        gc.mark_value(&self.recv);
        gc.mark_object(self.func);
    }
}

impl BoundMethod {
    pub fn new(recv: ObjPtr, func: Value) -> Self {
        let func = func.try_as_object().unwrap();
        assert!(unsafe { func.as_ref() }.is_callable(), "{:?}", func);

        Self {
            recv: Value::Object(recv),
            func,
        }
    }

    pub fn name(&self) -> &str {
        match unsafe { self.func.as_ref() } {
            Object::BoundMethod(m) => m.name(), // TODO: Is this even possible?
            Object::Closure(c) => &c.func.name,
            Object::HostFunc(f) => &f.name,
            _ => unreachable!(),
        }
    }
}
