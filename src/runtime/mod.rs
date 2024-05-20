use std::{collections::BTreeMap, ops::Range};
use tracing::trace;

pub mod func;
pub mod heap;
pub mod host;
pub mod object;
pub mod strings;
pub mod upvalue;
pub mod value;

pub use func::{BoundMethod, Closure, HostFunc};
pub use heap::{Gc, GcRoots, Heap, ObjPtr, Trace};
pub use host::HostFn;
pub use object::{Instance, List, Object, Type};
pub use strings::{InternedString, Strings};
pub use upvalue::{Upvalue, Upvalues};
pub use value::{Value, ValueType};

#[derive(Default)]
pub struct Runtime {
    stack: Vec<Value>,
    globals: BTreeMap<String, Value>,
    builtins: BTreeMap<String, Value>,

    upvalues: Upvalues,
    strings: Strings,
    heap: Heap,
}

pub type RuntimeResult<T> = Result<T, RuntimeError>;

#[derive(thiserror::Error, Debug)]
pub enum RuntimeError {
    #[error(
        "stack error: expected value at depth {}, but stack length was {}",
        depth,
        len
    )]
    NoValue { depth: usize, len: usize },

    #[error("name error: global variable `{}` was not defined", name)]
    UndefinedGlobal { name: String },

    #[error("name error: global variable `{}` was already declared", name)]
    RedeclaredGlobal { name: String },
}

// Stack
impl Runtime {
    pub fn push(&mut self, value: Value) {
        if let Value::Object(obj) = value {
            let obj = unsafe { obj.as_ref() };
            assert!(!obj.is_box());
            assert!(!obj.is_upvalue());
        }
        self.stack.push(value)
    }

    pub fn pop(&mut self) -> RuntimeResult<Value> {
        self.stack.pop().ok_or(RuntimeError::NoValue {
            depth: 0,
            len: self.stack.len(),
        })
    }

    pub fn pop_n(&mut self, n: usize) -> RuntimeResult<Vec<Value>> {
        let len = self.stack_offset(n)?;

        let popped = self.stack.split_off(len);
        Ok(popped)
    }

    pub fn pop_frame(&mut self, bp: usize) {
        self.stack.truncate(bp)
    }

    pub fn peek(&self, depth: usize) -> RuntimeResult<&Value> {
        self.stack.rget(depth).ok_or(RuntimeError::NoValue {
            depth,
            len: self.stack.len(),
        })
    }

    pub fn stack_get(&self, idx: usize) -> &Value {
        self.stack.get(idx).unwrap()
    }

    pub fn stack_put(&mut self, idx: usize, value: Value) {
        self.stack[idx] = value;
    }

    pub fn argv(&self, argc: usize) -> &[Value] {
        let start = self.stack.len().checked_sub(argc).unwrap();
        &self.stack[start..]
    }

    pub fn stack_offset(&self, n: usize) -> RuntimeResult<usize> {
        let len = self.stack.len();
        len.checked_sub(n)
            .ok_or(RuntimeError::NoValue { depth: n, len })
    }

    pub fn stack_len(&self) -> usize {
        self.stack.len()
    }

    pub fn trace_stack(&self) {
        for (slot, value) in self.stack.iter().enumerate() {
            trace!({ ?slot, %value }, "stack");
        }
    }

    pub fn stack_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn replace(&mut self, n: usize, value: Value) -> RuntimeResult<()> {
        let pos = self.stack_offset(n)?;
        self.stack[pos] = value;
        Ok(())
    }

    pub fn insert_as(&mut self, n: usize, value: Value) -> RuntimeResult<()> {
        let pos = self.stack_offset(n)?;
        self.stack.insert(pos, value);
        Ok(())
    }
}

// Globals
impl Runtime {
    pub fn define_global(&mut self, name: String, value: Value) -> RuntimeResult<()> {
        match self.globals.insert(name.clone(), value) {
            Some(_prev) => Err(RuntimeError::RedeclaredGlobal { name }),
            None => Ok(()),
        }
    }

    pub fn set_global(&mut self, name: String, value: Value) -> RuntimeResult<()> {
        match self.globals.get_mut(&name) {
            Some(dest) => {
                *dest = value;
                Ok(())
            }
            None => Err(RuntimeError::UndefinedGlobal { name }),
        }
    }

    pub fn get_global(&self, name: &str) -> RuntimeResult<&Value> {
        match self.globals.get(name) {
            Some(value) => Ok(value),
            None => Err(RuntimeError::UndefinedGlobal { name: name.into() }),
        }
    }

    pub fn get_global_mut(&mut self, name: &str) -> RuntimeResult<&mut Value> {
        match self.globals.get_mut(name) {
            Some(value) => Ok(value),
            None => Err(RuntimeError::UndefinedGlobal { name: name.into() }),
        }
    }
}

// Builtins
impl Runtime {
    pub fn define_builtin(&mut self, name: String, value: Value) {
        let prev = self.builtins.insert(name, value);
        assert_eq!(prev, None);
    }

    pub fn get_builtin(&self, name: &str) -> &Value {
        self.builtins.get(name).unwrap()
    }
}

// Upvalues
impl Runtime {
    pub fn capture_local(&mut self, slot: usize) -> ObjPtr {
        trace!({ ?slot, value = ?self.stack[slot]}, "capture local");

        let roots = GcRoots::new(&self.stack, &self.globals, &self.builtins);
        self.upvalues.capture(&mut self.heap, roots, slot)
    }

    pub fn recapture_upvalue(&mut self, bp: usize, index: usize) -> ObjPtr {
        let enclosing = self.stack[bp].try_as_object_ref().unwrap();
        let enclosing = unsafe { enclosing.as_ref() }.try_as_closure_ref().unwrap();

        let ptr = enclosing.upvalues[index];

        {
            let upvalue = unsafe { ptr.as_ref() };
            assert!(upvalue.is_upvalue());
            trace!({ ?enclosing, ?index, ?ptr, ?upvalue}, "capture parent");
        }

        ptr
    }

    pub fn close_upvalues(&mut self, len: usize) {
        self.close_upvalues_range(len..self.stack.len())
    }

    pub fn close_upvalues_range(&mut self, range: Range<usize>) {
        trace!({ ?range }, "closing upvalues");

        let roots = GcRoots::new(&self.stack, &self.globals, &self.builtins);
        self.upvalues
            .close(&mut self.heap, roots, &self.stack, range);
    }
}

// Strings
impl Runtime {
    pub fn intern(&mut self, s: &String) -> InternedString {
        self.strings.intern_ref(s)
    }

    pub fn concatenate(&mut self, a: InternedString, b: InternedString) -> InternedString {
        self.strings.concatenate(a, b)
    }
}

// Heap
impl Runtime {
    pub fn alloc(&mut self, obj: Object) -> ObjPtr {
        let roots = GcRoots::new(&self.stack, &self.globals, &self.builtins);
        self.heap.claim(roots, obj)
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
