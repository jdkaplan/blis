use std::collections::BTreeMap;
use std::fmt;

use crate::runtime::{Closure, Gc, Trace, Upvalue, Value};

#[derive(Debug, strum::EnumTryAs)]
pub enum Object {
    Box(*mut Value),
    Closure(Closure),
    Upvalue(Upvalue),
    Type(Type),
    Instance(Instance),

    #[cfg(feature = "gc_tombstone")]
    Tombstone,
}

impl fmt::Display for Object {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Object::Box(ptr) => {
                let v = unsafe { &**ptr };
                write!(f, "{}", v)
            }
            Object::Closure(o) => write!(f, "closure {}", o.func.name),
            Object::Upvalue(_) => write!(f, "upvalue"),
            Object::Type(_) => write!(f, "type"),
            Object::Instance(_) => write!(f, "instance"),

            #[cfg(feature = "gc_tombstone")]
            Object::Tombstone => unreachable!(),
        }
    }
}

impl Trace for Object {
    fn trace(&self, gc: &mut Gc) {
        match self {
            Object::Box(v) => gc.mark_value(unsafe { &**v }),
            Object::Closure(v) => v.trace(gc),
            Object::Upvalue(v) => v.trace(gc),
            Object::Type(v) => v.trace(gc),
            Object::Instance(v) => v.trace(gc),

            #[cfg(feature = "gc_tombstone")]
            Object::Tombstone => unreachable!(),
        }
    }
}

macro_rules! impl_as_obj {
    ($Var:path, $Ty:ty, $is:ident, $as_ref:ident, $as_mut:ident) => {
        pub fn $is(&self) -> bool {
            match self {
                $Var(_) => true,
                _ => false,
            }
        }

        pub fn $as_ref(&self) -> &$Ty {
            match self {
                $Var(v) => v,
                obj => unreachable!("{:?}", obj),
            }
        }

        pub fn $as_mut(&mut self) -> &mut $Ty {
            match self {
                $Var(v) => v,
                obj => unreachable!("{:?}", obj),
            }
        }
    };
}

impl Object {
    impl_as_obj!(Object::Box, *mut Value, is_box, as_box, as_box_mut);
    impl_as_obj!(
        Object::Upvalue,
        Upvalue,
        is_upvalue,
        as_upvalue,
        as_upvalue_mut
    );
    impl_as_obj!(
        Object::Closure,
        Closure,
        is_closure,
        as_closure,
        as_closure_mut
    );
    impl_as_obj!(Object::Type, Type, is_type, as_type, as_type_mut);
    impl_as_obj!(
        Object::Instance,
        Instance,
        is_instance,
        as_instance,
        as_instance_mut
    );
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
        let Value::Object(obj) = ty else {
            unreachable!()
        };

        assert!(unsafe { &*obj }.is_type());

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
