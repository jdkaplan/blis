use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use tracing::trace;

use crate::runtime::Value;

#[derive(Debug, Clone)]
pub enum Upvalue {
    Stack(usize),
    Heap(Arc<Mutex<Value>>),
}

#[derive(Debug, Clone)]
pub struct Upvalues {
    upvalues: Vec<Arc<Mutex<Upvalue>>>,
    gc_at: usize,
}

impl Default for Upvalues {
    fn default() -> Self {
        Self {
            // TODO: tune
            upvalues: Vec::with_capacity(16),
            gc_at: 16,
        }
    }
}

impl Upvalues {
    pub fn capture(&mut self, idx: usize) -> Arc<Mutex<Upvalue>> {
        self.gc();

        let upvalue = Upvalue::Stack(idx);
        let arc = Arc::new(Mutex::new(upvalue));
        self.upvalues.push(arc.clone());
        arc
    }

    pub fn close(&mut self, stack: &[Value], len: usize) {
        self.gc();

        let mut ptrs: BTreeMap<usize, Arc<Mutex<Value>>> = BTreeMap::new();

        for upvalue in &self.upvalues {
            let mut upvalue = upvalue.lock().unwrap();

            let Upvalue::Stack(slot) = *upvalue else {
                // This was already closed.
                continue;
            };

            if slot < len {
                // This one stays alive for now.
                continue;
            }

            // This _MUST_ reuse a pointer that was just created for it.
            if let Some(ptr) = ptrs.get(&slot) {
                *upvalue = Upvalue::Heap(ptr.clone());
                continue;
            }

            let value = stack[slot].clone();
            trace!({ ?slot, %value }, "close upvalue");

            let ptr = Arc::new(Mutex::new(value));
            ptrs.insert(slot, ptr.clone());
            *upvalue = Upvalue::Heap(ptr);
        }
    }

    fn gc(&mut self) {
        let limit = if cfg!(feature = "gc_stress") {
            0
        } else {
            self.gc_at
        };

        if self.upvalues.len() > limit {
            self.remove_unreachable();
        }
    }

    pub fn remove_unreachable(&mut self) {
        let before = self.upvalues.len();

        self.upvalues.retain(|arc| Arc::strong_count(arc) > 1);

        let after = self.upvalues.len();
        self.gc_at = 2 * after;
        trace!({ %before, %after, next_gc=self.gc_at }, "Upvalues::remove_unreachable");
    }
}
