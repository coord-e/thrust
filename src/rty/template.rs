use std::collections::HashMap;

use crate::chc;

use super::{RefinedType, RefinedTypeVar, Type};

#[derive(Debug, Clone)]
pub struct Template<FV> {
    pred_sig: chc::PredSig,
    atom_args: Vec<chc::Term<RefinedTypeVar<FV>>>,
    ty: Type,
}

impl<FV> Template<FV> {
    pub fn into_refined_type<F>(self, pred_var_generator: F) -> RefinedType<FV>
    where
        F: FnOnce(chc::PredSig) -> chc::PredVarId,
    {
        let pred_var = pred_var_generator(self.pred_sig);
        RefinedType {
            ty: self.ty,
            refinement: chc::Atom::new(pred_var.into(), self.atom_args),
        }
    }
}

#[derive(Debug, Clone)]
pub struct TemplateBuilder<FV> {
    dependencies: HashMap<RefinedTypeVar<FV>, chc::Sort>,
}

impl<FV> Default for TemplateBuilder<FV> {
    fn default() -> Self {
        TemplateBuilder {
            dependencies: HashMap::default(),
        }
    }
}

impl<FV> TemplateBuilder<FV>
where
    FV: Eq + std::hash::Hash,
{
    pub fn add_dependency(&mut self, v: FV, sort: chc::Sort) {
        self.dependencies.insert(RefinedTypeVar::Free(v), sort);
    }

    pub fn build(mut self, ty: Type) -> Template<FV> {
        self.dependencies
            .insert(RefinedTypeVar::Value, ty.to_sort());
        let mut atom_args = Vec::new();
        let mut pred_sig = chc::PredSig::new();
        for (v, sort) in self.dependencies.into_iter() {
            if sort.is_singleton() {
                continue;
            }
            atom_args.push(chc::Term::Var(v));
            pred_sig.push(sort);
        }
        Template {
            pred_sig,
            atom_args,
            ty,
        }
    }
}
