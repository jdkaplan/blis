use std::collections::{BTreeMap, BTreeSet, VecDeque};

use tracing::trace;

use crate::runtime::{Object, Value};

pub trait Trace {
    fn trace(&self, gc: &mut Gc);
}

#[derive(Debug, Default)]
pub struct Heap {
    objects: BTreeSet<*mut Object>,
    gc_at: usize,
}

impl Heap {
    pub fn new(first_gc: usize) -> Self {
        Self {
            gc_at: first_gc,
            ..Default::default()
        }
    }

    pub fn claim(&mut self, roots: GcRoots<'_, '_>, obj: Object) -> *mut Object {
        let limit = if cfg!(feature = "gc_stress") {
            0
        } else {
            self.gc_at
        };

        self.collect_garbage(&obj, roots, limit);
        self.alloc(obj)
    }

    /// Always `*mut Object::Box(_)`
    pub fn claim_value(&mut self, roots: GcRoots<'_, '_>, v: Value) -> *mut Object {
        let ptr = Box::into_raw(Box::new(v));
        self.claim(roots, Object::Box(ptr))
    }
}

impl Heap {
    fn alloc(&mut self, obj: Object) -> *mut Object {
        trace!({ ?obj }, "alloc");

        let ptr = Box::into_raw(Box::new(obj));

        assert!(self.objects.insert(ptr));
        trace!({ ?ptr }, "alloc");

        ptr
    }

    fn dealloc(&mut self, ptr: *mut Object) {
        assert!(self.objects.remove(&ptr));
        trace!({ ?ptr }, "dealloc");

        match unsafe { &*ptr } {
            Object::Box(ptr) => {
                let v = unsafe { Box::from_raw(*ptr) };
                drop(v)
            }
            _ => {
                // No more untracked references
            }
        }

        #[cfg(feature = "gc_tombstone")]
        unsafe {
            *ptr = Object::Tombstone;
        }

        #[cfg(not(feature = "gc_tombstone"))]
        unsafe {
            let _ = Box::from_raw(ptr);
        }
    }

    fn collect_garbage(&mut self, obj: &Object, roots: GcRoots, limit: usize) {
        let size = self.objects.len();
        if size < limit {
            trace!({ %size, %limit }, "gc skipped");
            return;
        }

        trace!({ %size }, "gc start");

        let mut gc = Gc::default();

        // Mark the roots
        for root in roots.stack {
            gc.mark_value(root);
        }
        for root in roots.globals.values() {
            gc.mark_value(root);
        }
        if let Some(upvalues) = roots.upvalues {
            for root in upvalues {
                gc.mark_object(*root);
            }
        }

        // Trace the reachable graph
        obj.trace(&mut gc);
        while let Some(ptr) = gc.pending.pop_front() {
            let obj = unsafe { ptr.as_ref().unwrap() };

            obj.trace(&mut gc);
        }

        // Sweep unreachable objects (i.e., keep only marked)
        let unreachable: Vec<_> = self
            .objects
            .iter()
            .copied()
            .filter(|ptr| !gc.marked.contains(ptr))
            .collect();
        for ptr in unreachable {
            self.dealloc(ptr);
        }

        let after = self.objects.len();
        let next_gc = 2 * after;
        trace!({ before=size, %after, freed=(size-after), %next_gc }, "gc end");

        self.gc_at = next_gc;
    }
}

#[derive(Debug, Copy, Clone)]
pub struct GcRoots<'a, 'b> {
    stack: &'a [Value],
    globals: &'a BTreeMap<String, Value>,
    upvalues: Option<&'b [*mut Object]>, // *mut Object::Upvalue
}

impl<'a> GcRoots<'a, '_> {
    pub fn new(stack: &'a [Value], globals: &'a BTreeMap<String, Value>) -> Self {
        Self {
            stack,
            globals,
            upvalues: None,
        }
    }
}

impl<'a, 'b> GcRoots<'a, 'b> {
    pub fn with_upvalues<'u: 'b>(&self, upvalues: &'b [*mut Object]) -> Self {
        Self {
            upvalues: Some(upvalues),
            ..*self
        }
    }
}

#[derive(Default)]
pub struct Gc {
    pending: VecDeque<*mut Object>,
    marked: BTreeSet<*mut Object>,
}

impl Gc {
    pub fn mark_value(&mut self, value: &Value) {
        if let Value::Object(ptr) = value {
            self.mark_object(*ptr);
        }
    }

    pub fn mark_object(&mut self, ptr: *mut Object) {
        if self.marked.insert(ptr) {
            self.pending.push_back(ptr);
        }
    }
}
