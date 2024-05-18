use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::hash::Hash;
use std::rc::Rc;

use rustc_index::IndexVec;

use super::{Atom, Clause, Sort, TermVarIdx};

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
    var_indices: HashMap<Rc<dyn Key>, TermVarIdx>,
    body: Vec<Atom<TermVarIdx>>,
}

impl ClauseBuilder {
    pub fn add_dependency<T>(&mut self, v: T, sort: Sort)
    where
        T: Hash + Eq + 'static,
    {
        let idx = self.vars.push(sort);
        self.var_indices.insert(Rc::new(v), idx);
    }

    pub fn add_alias<T, U>(&mut self, v1: T, v2: U)
    where
        T: Hash + Eq + 'static,
        U: Hash + Eq + 'static,
    {
        let k: &dyn Key = &v1;
        let idx = *self.var_indices.get(k).expect("unbound var");
        self.var_indices.insert(Rc::new(v2), idx);
    }

    fn subst_var<T>(&self, v: T) -> TermVarIdx
    where
        T: Hash + Eq + 'static + std::fmt::Debug,
    {
        tracing::debug!(?v, "subst_var");
        let k: &dyn Key = &v;
        let t_name = std::any::type_name::<T>();
        *self
            .var_indices
            .get(k)
            .unwrap_or_else(|| panic!("unbound var ({t_name})"))
    }

    pub fn add_body<T>(&mut self, atom: Atom<T>) -> &mut Self
    where
        T: Hash + Eq + 'static + std::fmt::Debug,
    {
        let atom = atom.map_var(|v| self.subst_var(v));
        self.body.push(atom);
        self
    }

    pub fn build<T>(&self, head: Atom<T>) -> Clause
    where
        T: Hash + Eq + 'static + std::fmt::Debug,
    {
        let vars = self.vars.clone();
        let head = head.map_var(|v| self.subst_var(v));
        let body = self.body.clone();
        Clause { vars, head, body }
    }
}
