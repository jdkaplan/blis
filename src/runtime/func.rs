use std::sync::{Arc, Mutex};

use crate::bytecode::Func;
use crate::runtime::{Upvalue, Value};

pub type RuntimeFn = fn(argc: u8, argv: &[Value]) -> Value;

#[derive(Debug, Clone)]
pub struct HostFunc {
    pub name: String,
    pub inner: Arc<RuntimeFn>,
}

#[derive(Debug, Clone)]
pub struct Closure {
    pub func: Arc<Func>,
    pub upvalues: Vec<Arc<Mutex<Upvalue>>>,
}
