use crate::chc;

use super::{Refinement, Type};

pub trait ClauseBuilderExt {
    fn with_value_var<'a, T>(&'a mut self, ty: &Type<T>) -> RefinementClauseBuilder<'a>;
    fn with_mapped_value_var<T>(&mut self, v: T) -> RefinementClauseBuilder<'_>
    where
        T: chc::Var;
}

impl ClauseBuilderExt for chc::ClauseBuilder {
    fn with_value_var<'a, T>(&'a mut self, ty: &Type<T>) -> RefinementClauseBuilder<'a> {
        let ty_sort = ty.to_sort();
        let value_var = (!ty_sort.is_singleton()).then(|| self.add_var(ty_sort));
        RefinementClauseBuilder {
            builder: self,
            value_var,
        }
    }

    fn with_mapped_value_var<T>(&mut self, v: T) -> RefinementClauseBuilder<'_>
    where
        T: chc::Var,
    {
        let value_var = self.find_mapped_var(v);
        RefinementClauseBuilder {
            builder: self,
            value_var,
        }
    }
}

pub struct RefinementClauseBuilder<'a> {
    builder: &'a mut chc::ClauseBuilder,
    value_var: Option<chc::TermVarIdx>,
}

impl<'a> RefinementClauseBuilder<'a> {
    pub fn add_body<T>(self, refinement: Refinement<T>) -> Self
    where
        T: chc::Var,
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
        if let Some(value_var) = self.value_var {
            instantiator.value_var(value_var);
        }
        let chc::Body { atoms, formula } = instantiator.instantiate();
        for atom in atoms {
            self.builder.add_body(atom);
        }
        self.builder.add_body(formula);
        self
    }

    pub fn head<T>(self, refinement: Refinement<T>) -> Vec<chc::Clause>
    where
        T: chc::Var,
    {
        if refinement.has_existentials() {
            panic!("head refinement must not contain existentials");
        }
        let mut instantiator = refinement
            .map_var(|v| self.builder.mapped_var(v))
            .instantiate();
        if let Some(value_var) = self.value_var {
            instantiator.value_var(value_var);
        }
        let chc::Body { atoms, formula } = instantiator.instantiate();
        let mut cs = atoms
            .into_iter()
            .map(|a| self.builder.head(a))
            .collect::<Vec<_>>();
        if !formula.is_top() {
            cs.push({
                let mut builder = self.builder.clone();
                builder.add_body(formula.not()).head(chc::Atom::bottom())
            });
        }
        cs
    }
}
