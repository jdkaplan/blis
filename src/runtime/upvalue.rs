use std::collections::BTreeMap;
use std::ops::Range;

use tracing::{instrument, trace};

use crate::runtime::{Gc, GcRoots, Heap, ObjPtr, Object, Trace, Value};

#[derive(Debug, Clone)]
pub enum Upvalue {
    Stack(usize),
    Heap(ObjPtr), // Object::Box(_)
}

impl Trace for Upvalue {
    fn trace(&self, gc: &mut Gc) {
        match self {
            Upvalue::Stack(_) => {
                // The whole stack is already marked.
            }

            Upvalue::Heap(obj) => {
                gc.mark_object(*obj);
            }
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct Upvalues {
    open: Vec<ObjPtr>, // Object::Upvalue(_)
}

impl Upvalues {
    /// Always `Object::Upvalue(_)`
    #[instrument(level = "trace", skip(self))]
    pub fn capture(&mut self, heap: &mut Heap, roots: GcRoots<'_, '_>, slot: usize) -> ObjPtr {
        let upvalue = Upvalue::Stack(slot);
        let obj = Object::Upvalue(upvalue);

        let ptr = heap.claim(roots, obj);
        self.open.push(ptr);
        ptr
    }

    #[instrument(level = "trace", skip(self))]
    pub fn close(
        &mut self,
        heap: &mut Heap,
        roots: GcRoots<'_, '_>,
        stack: &[Value],
        range: Range<usize>,
    ) {
        trace!({ ?range, stack=stack.len(), open=self.open.len() }, "close upvalues");

        let upvalues = std::mem::take(&mut self.open);
        let mut closed: BTreeMap<usize, ObjPtr> = BTreeMap::new();

        let roots = roots.with_upvalues(&upvalues);

        for ptr in upvalues.iter().copied() {
            let slot = {
                let upvalue = unsafe { ptr.as_ref() }.try_as_upvalue_ref().unwrap();
                let Upvalue::Stack(slot) = *upvalue else {
                    panic!("closed upvalue in open set: {:?}", upvalue);
                };
                slot
            };

            if range.contains(&slot) {
                trace!({ ?ptr, ?slot, value = ?&stack[slot] }, "keep open");
                self.open.push(ptr);
                continue;
            }

            // This _MUST_ reuse a value box that was just created for it.
            let boxed = if let Some(&boxed) = closed.get(&slot) {
                boxed
            } else {
                let value = stack[slot].clone();
                trace!({ ?ptr, ?slot, %value }, "close upvalue");

                let boxed = heap.claim_value(roots, value);
                closed.insert(slot, boxed);
                boxed
            };

            let upvalue = unsafe { ptr.as_mut() }.try_as_upvalue_mut().unwrap();
            *upvalue = Upvalue::Heap(boxed);
        }
    }
}
