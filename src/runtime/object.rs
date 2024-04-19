use std::collections::{BTreeMap, BTreeSet, VecDeque};

use slotmap::HopSlotMap;

use crate::runtime::Value;

slotmap::new_key_type! { pub struct ObjectId; }

#[derive(Debug, Default)]
pub struct Heap {
    objects: HopSlotMap<ObjectId, Object>,
}

impl Heap {
    pub fn gc(&mut self, roots: &[ObjectId]) {
        let mut gc = Gc::default();

        // Mark the roots
        for id in roots {
            gc.mark_object(*id);
        }

        // Trace the reachable graph
        while let Some(id) = gc.pending.pop_front() {
            let obj = &self.objects[id];
            obj.trace(&mut gc);
        }

        // Sweep unreachable objects (i.e., keep only marked)
        self.objects.retain(|k, _v| gc.marked.contains(&k));
    }
}

#[derive(Default)]
pub struct Gc {
    pending: VecDeque<ObjectId>,
    marked: BTreeSet<ObjectId>,
}

impl Gc {
    pub fn mark_value(&mut self, value: &Value) {
        if let Value::Object(id) = value {
            self.mark_object(*id);
        }
    }

    pub fn mark_object(&mut self, id: ObjectId) {
        if self.marked.insert(id) {
            self.pending.push_back(id);
        }
    }
}

#[derive(Debug)]
pub struct Object {
    pub fields: BTreeMap<String, Value>,
}

impl Object {
    fn trace(&self, gc: &mut Gc) {
        for v in self.fields.values() {
            gc.mark_value(v);
        }
    }
}
