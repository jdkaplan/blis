use std::collections::BTreeSet;
use std::sync::Arc;

use tracing::trace;

pub type InternedString = Arc<String>;

#[derive(Debug, Clone)]
pub struct Strings {
    interned: BTreeSet<Arc<String>>,
    gc_at: usize,
}

impl Default for Strings {
    fn default() -> Self {
        Self {
            interned: Default::default(),
            gc_at: 16, // TODO: tune
        }
    }
}

impl Strings {
    pub fn intern_owned(&mut self, s: String) -> InternedString {
        self.gc();

        if let Some(arc) = self.interned.get(&s) {
            arc.clone()
        } else {
            let arc = Arc::new(s);
            self.interned.insert(arc.clone());
            arc
        }
    }

    pub fn intern_ref(&mut self, s: &String) -> InternedString {
        self.gc();

        if let Some(arc) = self.interned.get(s) {
            arc.clone()
        } else {
            let arc = Arc::new(s.clone());
            self.interned.insert(arc.clone());
            arc
        }
    }

    pub fn concatenate(&mut self, a: InternedString, b: InternedString) -> InternedString {
        self.gc();

        let mut c = String::with_capacity(a.len() + b.len());
        c.push_str(&a);
        c.push_str(&b);
        self.intern_owned(c)
    }

    fn gc(&mut self) {
        let limit = if cfg!(feature = "gc_stress") {
            0
        } else {
            self.gc_at
        };

        if self.interned.len() > limit {
            self.remove_unreachable();
        }
    }

    pub fn remove_unreachable(&mut self) {
        let before = self.interned.len();

        self.interned.retain(|arc| Arc::strong_count(arc) > 1);

        let after = self.interned.len();
        self.gc_at = 2 * after;
        trace!({ %before, %after, next_gc=self.gc_at }, "Strings::remove_unreachable");
    }
}
