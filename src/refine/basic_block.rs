//! The refinement type for a basic block.

use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_middle::ty as mir_ty;

use crate::rty;

#[derive(Debug, Clone)]
pub enum BasicBlockTypeParamKind {
    Local(Local, mir_ty::Mutability),
    OuterFnParam(rty::FunctionParamIdx),
    Synthetic,
}

impl BasicBlockTypeParamKind {
    pub fn local(&self) -> Option<Local> {
        match self {
            BasicBlockTypeParamKind::Local(local, _) => Some(*local),
            _ => None,
        }
    }

    pub fn outer_fn_param_idx(&self) -> Option<rty::FunctionParamIdx> {
        match self {
            BasicBlockTypeParamKind::OuterFnParam(idx) => Some(*idx),
            _ => None,
        }
    }
}

/// A special case of [`rty::FunctionType`] whose parameters are associated with [`Local`]s.
///
/// Thrust handles basic blocks as functions, but it needs to associate function
/// parameters with MIR [`Local`]s during its analysis. [`BasicBlockType`] includes this mapping
/// from function parameters to [`Local`]s, along with the underlying function type.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    // TODO: make this completely private by exposing appropriate ctor
    pub(super) ty: rty::FunctionType,
    pub(super) locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
    // XXX: needs this to disambiguate synthetic unit param from outer fn unit param
    pub(super) outer_fn_param_count: usize,
}

impl<'a, D> Pretty<'a, D, termcolor::ColorSpec> for &BasicBlockType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        let params = self.ty.params.iter_enumerated().map(|(idx, ty)| {
            if let Some((local, mutbl)) = self.locals.get(idx) {
                allocator
                    .text(format!("{}{:?}:", mutbl.prefix_str(), local))
                    .append(allocator.space())
                    .append(ty.pretty(allocator))
            } else {
                ty.pretty(allocator)
            }
        });
        allocator
            .intersperse(params, separator)
            .parens()
            .append(allocator.space())
            .append(allocator.text("→"))
            .append(allocator.line())
            .append(self.ty.ret.pretty(allocator))
            .group()
    }
}

impl AsRef<rty::FunctionType> for BasicBlockType {
    fn as_ref(&self) -> &rty::FunctionType {
        &self.ty
    }
}

impl BasicBlockType {
    pub fn param_kind(&self, idx: rty::FunctionParamIdx) -> BasicBlockTypeParamKind {
        if let Some((local, mutbl)) = self.locals.get(idx) {
            BasicBlockTypeParamKind::Local(*local, *mutbl)
        } else if idx.index() >= self.locals.len() && self.outer_fn_param_count > 0 {
            BasicBlockTypeParamKind::OuterFnParam(rty::FunctionParamIdx::from(
                idx.index() - self.locals.len(),
            ))
        } else {
            BasicBlockTypeParamKind::Synthetic
        }
    }

    pub fn local_of_param(&self, idx: rty::FunctionParamIdx) -> Option<Local> {
        self.param_kind(idx).local()
    }

    pub fn mutbl_of_param(&self, idx: rty::FunctionParamIdx) -> Option<mir_ty::Mutability> {
        if let BasicBlockTypeParamKind::Local(_, mutbl) = self.param_kind(idx) {
            Some(mutbl)
        } else {
            None
        }
    }

    pub fn local_params(&self) -> impl DoubleEndedIterator<Item = rty::FunctionParamIdx> + '_ {
        self.locals.indices()
    }

    pub fn locals(&self) -> impl Iterator<Item = Local> + '_ {
        self.ty
            .params
            .iter_enumerated()
            .filter_map(|(idx, _)| self.local_of_param(idx))
    }

    pub fn param_of_local(&self, local: Local) -> Option<rty::FunctionParamIdx> {
        self.locals
            .iter_enumerated()
            .find_map(|(idx, (l, _))| if *l == local { Some(idx) } else { None })
    }

    pub fn param_of_outer_fn_param(
        &self,
        idx: rty::FunctionParamIdx,
    ) -> Option<rty::FunctionParamIdx> {
        if idx.index() < self.outer_fn_param_count {
            Some(rty::FunctionParamIdx::from(self.locals.len() + idx.index()))
        } else {
            None
        }
    }

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }

    pub fn set_precondition(&mut self, refinement: rty::Refinement<rty::FunctionParamIdx>) {
        let last_param_idx = self.ty.params.last_index().unwrap();
        let refinement = refinement.map_var(|v| {
            if v == rty::RefinedTypeVar::Free(last_param_idx) {
                rty::RefinedTypeVar::Value
            } else {
                v
            }
        });
        self.ty
            .params
            .raw
            .last_mut()
            .unwrap()
            .refinement
            .push_conj(refinement);
    }

    /// Inner function type of BasicBlockType contains extra parameters that carry original
    /// function parameter values. `truncate_outer_fn_params` removes these extra parameters
    /// to subtype output of [`BasicBlockType::to_function_ty`] against the function type.
    ///
    /// before: (_1: int, _2: int, int, { int |  p4 ν $0 $1 $2 }) → { int | p5 ν $0 $1 $2 $3 }
    /// after:  (_1: int, _2: { int | p4 v $0 $1 $0 }) → { int | p5 ν $0 $1 _1 _2 }
    ///
    /// FIXME: this should be (&self) -> FunctionType
    pub fn truncate_outer_fn_params(&mut self) {
        let last_param_idx = self.ty.params.last_index().unwrap();
        let last_param_ty = self.ty.params.raw.last().unwrap();

        let mut mapping = HashMap::new();
        for (idx, param_ty) in self.ty.params.iter_enumerated() {
            let mapped_idx = if let Some(outer_idx) = self.param_kind(idx).outer_fn_param_idx() {
                let corresponding_local = crate::analyze::local_of_function_param(outer_idx);
                self.param_of_local(corresponding_local).unwrap()
            } else {
                idx
            };
            mapping.insert(idx, mapped_idx);

            // to be sure
            if idx != last_param_idx {
                assert!(param_ty.refinement.is_top());
            }
        }

        let last_param_refinement = last_param_ty.refinement.clone().map_var(|v| {
            let idx = match v {
                rty::RefinedTypeVar::Free(idx) => idx,
                rty::RefinedTypeVar::Value => last_param_idx,
                v => return v,
            };
            let mapped_idx = mapping[&idx];
            if Some(mapped_idx) == self.locals.last_index() {
                rty::RefinedTypeVar::Value
            } else {
                rty::RefinedTypeVar::Free(mapped_idx)
            }
        });

        if !self.locals.is_empty() {
            self.ty.params.truncate(self.locals.len());
        }

        self.ty.params.raw.last_mut().unwrap().refinement = last_param_refinement;
        self.ty.ret.refinement = self
            .ty
            .ret
            .refinement
            .clone()
            .map_free_var(|idx| mapping[&idx]);
    }
}
