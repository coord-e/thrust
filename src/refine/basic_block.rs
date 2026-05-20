//! The refinement type for a basic block.

use std::collections::HashMap;

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_middle::ty as mir_ty;

use crate::rty;

/// A special case of [`rty::FunctionType`] whose parameters are associated with [`Local`]s.
///
/// Thrust handles basic blocks as functions, but it needs to associate function
/// parameters with MIR [`Local`]s during its analysis. [`BasicBlockType`] includes this mapping
/// from function parameters to [`Local`]s, along with the underlying function type.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    pub ty: rty::FunctionType,
    pub locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
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
    pub fn local_of_param(&self, idx: rty::FunctionParamIdx) -> Option<Local> {
        self.locals.get(idx).map(|(local, _)| *local)
    }

    pub fn mutbl_of_param(&self, idx: rty::FunctionParamIdx) -> Option<mir_ty::Mutability> {
        self.locals.get(idx).map(|(_, mutbl)| *mutbl)
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

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }

    // Inner function type of BasicBlockType contains extra parameters that carry original
    // function parameter values. `truncate_outer_fn_params` removes these extra parameters
    // to subtype entry_ty against the function type.
    //
    // before: (_1: int, _2: int, int, { int |  p4 ν $0 $1 $2 }) → { int | p5 ν $0 $1 $2 $3 }
    // after:  (_1: int, _2: { int | p4 v $0 $1 $0 }) → { int | p5 ν $0 $1 _1 _2 }
    pub fn truncate_outer_fn_params(&mut self) {
        let last_param_idx = self.as_ref().params.last_index().unwrap();
        let last_param_ty = self.as_ref().params.raw.last().unwrap();

        let mut mapping = HashMap::new();
        for (idx, param_ty) in self.as_ref().params.iter_enumerated() {
            let mapped_idx = if idx >= self.locals.next_index() {
                let outer_fn_param_idx =
                    rty::FunctionParamIdx::from(idx.index() - self.locals.len());
                let corresponding_local = Local::from(outer_fn_param_idx.index() + 1);
                self.param_of_local(corresponding_local).unwrap_or_else(|| {
                    // XXX: if local-param is empty and there are some outer fn param,
                    //      idx == $0, corresponding_local is _1 and param_of_local returns None
                    assert!(idx.index() == 0);
                    idx
                })
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
