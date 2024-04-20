use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    fmt,
};

use slotmap::HopSlotMap;

use crate::runtime::Value;

slotmap::new_key_type! { pub struct ObjectId; }

impl fmt::Display for ObjectId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{:?}", self.0)
    }
}

#[derive(Debug, Default)]
pub struct Heap {
    objects: HopSlotMap<ObjectId, Object>,
}

impl Heap {
    pub fn make_object(&mut self) -> ObjectId {
        self.objects.insert(Object::default())
    }

    pub fn get_mut(&mut self, id: ObjectId) -> Option<&mut Object> {
        self.objects.get_mut(id)
    }

    pub fn get(&self, id: ObjectId) -> Option<&Object> {
        self.objects.get(id)
    }

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

#[derive(Debug, Default)]
pub struct Object {
    pub fields: BTreeMap<String, Value>,
}

impl Object {
    pub fn get_field(&self, name: &str) -> &Value {
        &self.fields[name]
    }

    pub fn set_field(&mut self, name: String, value: Value) {
        self.fields.insert(name, value);
    }
}

impl Object {
    fn trace(&self, gc: &mut Gc) {
        for v in self.fields.values() {
            gc.mark_value(v);
        }
    }
}
