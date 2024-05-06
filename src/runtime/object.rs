use std::collections::BTreeMap;
use std::fmt;

use crate::runtime::{BoundMethod, Closure, Gc, HostFunc, Trace, Upvalue, Value};

#[derive(Debug, strum::EnumIs, strum::EnumTryAs)]
pub enum Object {
    // Upvalues
    Box(*mut Value),
    Upvalue(Upvalue),

    // Functions
    BoundMethod(BoundMethod),
    Closure(Closure),
    HostFunc(HostFunc),

    // Objects
    Instance(Instance),
    Type(Type),

    #[cfg(feature = "gc_tombstone")]
    Tombstone,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Upvalue(_) => write!(f, "upvalue"),
            Object::Box(ptr) => {
                let v = unsafe { &**ptr };
                write!(f, "{}", v)
            }

            Object::BoundMethod(_) => write!(f, "bound method"), // TODO: show name
            Object::Closure(o) => write!(f, "closure {}", o.func.name),
            Object::HostFunc(v) => write!(f, "func {:?}", v.name),

            Object::Type(t) => write!(f, "type {}", t.name),

            Object::Instance(i) => {
                let ty = i.ty.try_as_object_ref().unwrap();
                let ty = unsafe { &**ty }.try_as_type_ref().unwrap();
                write!(f, "instance of {}", ty.name)
            }

            #[cfg(feature = "gc_tombstone")]
            Object::Tombstone => panic!("use after free"),
        }
    }
}

impl Trace for Object {
    fn trace(&self, gc: &mut Gc) {
        match self {
            Object::Box(v) => gc.mark_value(unsafe { &**v }),

            Object::BoundMethod(v) => v.trace(gc),
            Object::Closure(v) => v.trace(gc),
            Object::HostFunc(v) => v.trace(gc),
            Object::Instance(v) => v.trace(gc),
            Object::Type(v) => v.trace(gc),
            Object::Upvalue(v) => v.trace(gc),

            #[cfg(feature = "gc_tombstone")]
            Object::Tombstone => panic!("use after free"),
        }
    }
}

#[derive(Debug)]
pub struct Type {
    pub name: String,
    pub methods: BTreeMap<String, Value>,
}

impl Trace for Type {
    fn trace(&self, gc: &mut Gc) {
        for v in self.methods.values() {
            gc.mark_value(v);
        }
    }
}

impl Type {
    pub fn new(name: String) -> Self {
        Self {
            name,
            methods: BTreeMap::new(),
        }
    }

    pub fn get_method(&self, name: &str) -> Option<&Value> {
        self.methods.get(name)
    }

    pub fn set_method(&mut self, name: String, value: Value) {
        self.methods.insert(name, value);
    }
}

#[derive(Debug)]
pub struct Instance {
    pub ty: Value,
    pub fields: BTreeMap<String, Value>,
}

impl Trace for Instance {
    fn trace(&self, gc: &mut Gc) {
        gc.mark_value(&self.ty);

        for v in self.fields.values() {
            gc.mark_value(v);
        }
    }
}

impl Instance {
    pub fn new(ty: Value) -> Self {
        let obj = ty.try_as_object_ref().unwrap();

        assert!(unsafe { &**obj }.is_type());

        Self {
            ty,
            fields: BTreeMap::new(),
        }
    }

    pub fn get_field(&self, name: &str) -> Option<&Value> {
        self.fields.get(name)
    }

    pub fn set_field(&mut self, name: String, value: Value) {
        self.fields.insert(name, value);
    }
}
