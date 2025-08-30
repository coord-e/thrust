//! A builder for [`Clause`]s.
//!
//! This module provides [`ClauseBuilder`], a helper for constructing [`Clause`]s. It is
//! particularly useful for managing the universally quantified variables of a clause. It can
//! automatically create fresh [`TermVarIdx`] for variables from other domains (e.g.,
//! [`crate::rty::FunctionParamIdx`]), simplifying the generation of clauses from higher-level
//! representations.

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::rc::Rc;

use rustc_index::IndexVec;

use super::{Atom, Body, Clause, DebugInfo, Sort, TermVarIdx};

/// A convenience trait to represent constraints on variables used in [`ClauseBuilder`] at once.
pub trait Var: Eq + Ord + Hash + Copy + Debug + 'static {}
impl<T: Eq + Ord + Hash + Copy + Debug + 'static> Var for T {}

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

/// A builder for a [`Clause`].
///
/// [`Clause`] contains a list of universally quantified variables, a head atom, and a body formula.
/// When building the head and body, we usually have some formulas that represents variables using
/// something other than [`TermVarIdx`] (e.g. [`crate::rty::FunctionParamIdx`] or [`crate::refine::Var`]).
/// These variables are usually OK to be universally quantified in the clause, so we want to keep
/// the mapping of them to [`TermVarIdx`] and use it to convert the variables in the formulas
/// during the construction of the clause.
///
/// Also see [`crate::rty::ClauseBuilderExt`], which provides a higher-level API on top of this
/// to build clauses from [`crate::rty::Refinement`]s.
#[derive(Clone, Default)]
pub struct ClauseBuilder {
    vars: IndexVec<TermVarIdx, Sort>,
    mapped_var_indices: HashMap<Rc<dyn Key>, TermVarIdx>,
    body: Body<TermVarIdx>,
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

    pub fn add_body(&mut self, body: impl Into<Body<TermVarIdx>>) -> &mut Self {
        self.body.push_conj(body);
        self
    }

    pub fn head(&self, head: Atom<TermVarIdx>) -> Clause {
        let vars = self.vars.clone();
        let mut body = self.body.clone();
        body.simplify();
        Clause {
            vars,
            head,
            body,
            debug_info: DebugInfo::from_current_span(),
        }
    }

    // Currently, variables are mapped by rty::Instantiator built from `mapped_var`
    // (see rty::RefinementClauseBuilder)
    // Maybe we should remove chc::ClauseBuilder and integrate it into rty::RefinementClauseBuilder
    //
    // pub fn add_body_mapped<T>(&mut self, atom: Atom<T>) -> &mut Self
    // where
    //     T: Var + Debug,
    // {
    //     self.add_body(atom.map_var(|v| self.mapped_var(v)))
    // }
    //
    // pub fn add_body_formula_mapped<T>(&mut self, formula: Formula<T>) -> &mut Self
    // where
    //     T: Var + Debug,
    // {
    //     self.add_body_formula(formula.map_var(|v| self.mapped_var(v)))
    // }
    //
    // pub fn head_mapped<T>(&self, head: Atom<T>) -> Clause
    // where
    //     T: Var + Debug,
    // {
    //     self.head(head.map_var(|v| self.mapped_var(v)))
    // }
}
