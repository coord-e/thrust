use std::fmt::Debug;
use std::hash::Hash;

use crate::chc;

use super::{Refinement, Type};

pub trait ClauseBuilderExt {
    fn with_value_var<'a>(&'a mut self, ty: &Type) -> RefinementClauseBuilder<'a>;
    fn with_mapped_value_var<'a, T>(&'a mut self, v: T) -> RefinementClauseBuilder<'a>
    where
        T: Hash + Eq + Debug + 'static;
}

impl ClauseBuilderExt for chc::ClauseBuilder {
    fn with_value_var<'a>(&'a mut self, ty: &Type) -> RefinementClauseBuilder<'a> {
        let value_var = self.add_var(ty.to_sort());
        RefinementClauseBuilder {
            builder: self,
            value_var,
        }
    }

    fn with_mapped_value_var<'a, T>(&'a mut self, v: T) -> RefinementClauseBuilder<'a>
    where
        T: Hash + Eq + Debug + 'static,
    {
        let value_var = self.find_mapped_var(v).unwrap();
        RefinementClauseBuilder {
            builder: self,
            value_var,
        }
    }
}

pub struct RefinementClauseBuilder<'a> {
    builder: &'a mut chc::ClauseBuilder,
    value_var: chc::TermVarIdx,
}

impl<'a> RefinementClauseBuilder<'a> {
    pub fn add_body<T>(self, refinement: Refinement<T>) -> Self
    where
        T: Hash + Eq + Debug + Clone + 'static,
    {
        let existentials: Vec<_> = refinement
            .existentials()
            .map(|(ev, sort)| (ev, sort.clone()))
            .collect();
        let mut instantiator = refinement
            .map_var(|v| self.builder.mapped_var(v))
            .instantiate();
        for (ev, sort) in existentials {
            let tv = self.builder.add_var(sort);
            instantiator.existential(ev, tv);
        }
        instantiator.value_var(self.value_var);
        for atom in instantiator.into_atoms() {
            self.builder.add_body(atom);
        }
        self
    }

    pub fn head<T>(self, refinement: Refinement<T>) -> chc::Clause
    where
        T: Hash + Eq + Debug + 'static,
    {
        if refinement.has_existentials() {
            panic!("head refinement must not contain existentials");
        }
        let mut instantiator = refinement
            .map_var(|v| self.builder.mapped_var(v))
            .instantiate();
        instantiator.value_var(self.value_var);
        let mut atoms: Vec<_> = instantiator.into_atoms().collect();
        if atoms.len() != 1 {
            panic!("head refinement must contain exactly one atom");
        }
        self.builder.head(atoms.pop().unwrap())
    }
}
