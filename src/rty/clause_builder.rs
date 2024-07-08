use std::fmt::Debug;
use std::hash::Hash;

use crate::chc;

use super::{RefinedTypeVar, Refinement, Type};

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
    fn refinement_to_atom<T>(&self, refinement: Refinement<T>) -> chc::Atom<chc::TermVarIdx>
    where
        T: Hash + Eq + Debug + 'static,
    {
        refinement.map_var(|v| match v {
            RefinedTypeVar::Value => self.value_var,
            RefinedTypeVar::Free(v) => self.builder.mapped_var(v),
        })
    }

    pub fn add_body<T>(self, refinement: Refinement<T>) -> Self
    where
        T: Hash + Eq + Debug + 'static,
    {
        let body = self.refinement_to_atom(refinement);
        self.builder.add_body(body);
        self
    }

    pub fn head<T>(self, refinement: Refinement<T>) -> chc::Clause
    where
        T: Hash + Eq + Debug + 'static,
    {
        let head = self.refinement_to_atom(refinement);
        self.builder.head(head)
    }
}
