use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::Rc;

use rustc_index::IndexVec;

use super::{Atom, Clause, DebugInfo, Sort, TermVarIdx};

pub trait Var: Eq + Hash + Copy + Debug + 'static {}
impl<T: Eq + Hash + Copy + Debug + 'static> Var for T {}

// https://stackoverflow.com/questions/64838355/how-do-i-create-a-hashmap-with-type-erased-keys
trait Key {
    fn eq(&self, other: &dyn Key) -> bool;
    fn hash(&self) -> u64;
    fn as_any(&self) -> &dyn Any;
}

impl<T: Eq + Hash + 'static> Key for T {
    fn eq(&self, other: &dyn Key) -> bool {
        if let Some(other) = other.as_any().downcast_ref::<T>() {
            return self == other;
        }
        false
    }

    fn hash(&self) -> u64 {
        let mut h = std::hash::DefaultHasher::new();
        // mix the typeid of T into the hash to make distinct types
        // provide distinct hashes
        Hash::hash(&(TypeId::of::<T>(), self), &mut h);
        std::hash::Hasher::finish(&h)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl PartialEq for dyn Key {
    fn eq(&self, other: &Self) -> bool {
        Key::eq(self, other)
    }
}

impl Eq for dyn Key {}

impl Hash for dyn Key {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let key_hash = Key::hash(self);
        std::hash::Hasher::write_u64(state, key_hash);
    }
}

#[derive(Clone, Default)]
pub struct ClauseBuilder {
    vars: IndexVec<TermVarIdx, Sort>,
    mapped_var_indices: HashMap<Rc<dyn Key>, TermVarIdx>,
    body: Vec<Atom<TermVarIdx>>,
}

impl ClauseBuilder {
    pub fn add_mapped_var<T>(&mut self, v: T, sort: Sort)
    where
        T: Var,
    {
        let idx = self.vars.push(sort);
        self.mapped_var_indices.insert(Rc::new(v), idx);
    }

    pub fn add_var(&mut self, sort: Sort) -> TermVarIdx {
        self.vars.push(sort)
    }

    pub fn find_mapped_var<T>(&self, v: T) -> Option<TermVarIdx>
    where
        T: Var,
    {
        let k: &dyn Key = &v;
        self.mapped_var_indices.get(k).copied()
    }

    pub fn mapped_var<T>(&self, v: T) -> TermVarIdx
    where
        T: Var + Debug,
    {
        let k: &dyn Key = &v;
        self.mapped_var_indices
            .get(k)
            .copied()
            .unwrap_or_else(|| panic!("unbound var {:?}", v))
    }

    pub fn add_body(&mut self, atom: Atom<TermVarIdx>) -> &mut Self {
        self.body.push(atom);
        self
    }

    pub fn add_body_mapped<T>(&mut self, atom: Atom<T>) -> &mut Self
    where
        T: Var + Debug,
    {
        self.add_body(atom.map_var(|v| self.mapped_var(v)))
    }

    pub fn head(&self, head: Atom<TermVarIdx>) -> Clause {
        let vars = self.vars.clone();
        let mut body: Vec<_> = self
            .body
            .clone()
            .into_iter()
            .filter(|a| !a.is_top())
            .collect();
        if body.is_empty() {
            body = vec![Atom::top()];
        } else if body.iter().any(Atom::is_bottom) {
            body = vec![Atom::bottom()];
        }
        Clause {
            vars,
            head,
            body,
            debug_info: DebugInfo::from_current_span(),
        }
    }

    pub fn head_mapped<T>(&self, head: Atom<T>) -> Clause
    where
        T: Var + Debug,
    {
        self.head(head.map_var(|v| self.mapped_var(v)))
    }
}
