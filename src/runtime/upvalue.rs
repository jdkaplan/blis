use std::ops::Index;
use std::slice::SliceIndex;
use std::sync::{Arc, Mutex};

use crate::runtime::Value;

#[derive(Debug, Clone, Default)]
pub struct Upvalues(Vec<Upvalue>);

impl Upvalues {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn push(&mut self, v: Upvalue) -> usize {
        let len = self.len();
        self.0.push(v);
        len
    }
}

impl<'a> IntoIterator for &'a mut Upvalues {
    type Item = &'a mut Upvalue;

    type IntoIter = std::slice::IterMut<'a, Upvalue>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<I: SliceIndex<[Upvalue]>> Index<I> for Upvalues {
    type Output = <Vec<Upvalue> as Index<I>>::Output;

    fn index(&self, index: I) -> &Self::Output {
        Index::index(&self.0, index)
    }
}

#[derive(Debug, Clone)]
pub enum Upvalue {
    Stack(usize),
    Heap(Arc<Mutex<Value>>),
}
