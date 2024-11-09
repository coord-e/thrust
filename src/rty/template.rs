use std::collections::BTreeMap;

use crate::chc;

use super::{RefinedType, RefinedTypeVar, Type};

#[derive(Debug, Clone)]
pub struct Template<FV> {
    pred_sig: chc::PredSig,
    atom_args: Vec<chc::Term<RefinedTypeVar<FV>>>,
    ty: Type<FV>,
}

impl<FV> Template<FV> {
    pub fn into_refined_type<F>(self, pred_var_generator: F) -> RefinedType<FV>
    where
        F: FnOnce(chc::PredSig) -> chc::PredVarId,
    {
        let pred_var = pred_var_generator(self.pred_sig);
        RefinedType::new(
            self.ty,
            chc::Atom::new(pred_var.into(), self.atom_args).into(),
        )
    }
}

#[derive(Debug, Clone)]
pub struct TemplateBuilder<FV> {
    dependencies: BTreeMap<RefinedTypeVar<FV>, chc::Sort>,
}

impl<FV> Default for TemplateBuilder<FV> {
    fn default() -> Self {
        TemplateBuilder {
            dependencies: Default::default(),
        }
    }
}

impl<FV> TemplateBuilder<FV>
where
    FV: chc::Var,
{
    pub fn add_dependency(&mut self, v: FV, sort: chc::Sort) {
        self.dependencies.insert(RefinedTypeVar::Free(v), sort);
    }

    pub fn build(mut self, ty: Type<FV>) -> Template<FV> {
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
