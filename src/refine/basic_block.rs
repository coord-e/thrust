//! The refinement type for a basic block.

use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::{self, Local};
use rustc_middle::ty as mir_ty;

use crate::chc;
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

    /// Replaces the type of every parameter that holds a parameter of the function with the type
    /// the signature of the function gives it.
    ///
    /// A signature can refine a type where the MIR type it is built from has nothing to say, as in
    /// `Vec<{ v: i32 | v > 0 }>` or in the pre- and postcondition of a function-typed parameter.
    /// The entry block is entered with the arguments of the call, so those are the types it takes.
    pub fn install_signature_types(
        &mut self,
        params: &IndexVec<rty::FunctionParamIdx, rty::RefinedType<rty::FunctionParamIdx>>,
    ) {
        let param_of_fn_param = |idx| {
            self.param_of_local(crate::analyze::local_of_function_param(idx))
                .expect("the entry block takes every parameter of the function")
        };
        let signature_types: Vec<_> = self
            .ty
            .params
            .indices()
            .filter_map(|idx| {
                let fn_param_idx = self.fn_param_of_param(idx)?;
                let ty = params[fn_param_idx]
                    .ty
                    .clone()
                    .subst_var(|idx| chc::Term::var(param_of_fn_param(idx)));
                Some((idx, ty))
            })
            .collect();
        for (idx, ty) in signature_types {
            self.ty.params[idx].ty = ty;
        }
    }

    /// The parameter of the function held by the parameter `idx`, if it holds one.
    fn fn_param_of_param(&self, idx: rty::FunctionParamIdx) -> Option<rty::FunctionParamIdx> {
        match self.param_kind(idx) {
            BasicBlockTypeParamKind::Local(local, _) if local != mir::RETURN_PLACE => {
                let fn_param_idx = crate::analyze::function_param_of_local(local);
                (fn_param_idx.index() < self.outer_fn_param_count).then_some(fn_param_idx)
            }
            BasicBlockTypeParamKind::OuterFnParam(fn_param_idx) => Some(fn_param_idx),
            _ => None,
        }
    }

    pub fn set_precondition(&mut self, refinement: rty::Refinement<rty::FunctionParamIdx>) {
        let last_param_idx = self.ty.params.last_index().unwrap();
        self.ty.params.raw.last_mut().unwrap().refinement = refinement.map_var(|v| {
            if v == rty::RefinedTypeVar::Free(last_param_idx) {
                rty::RefinedTypeVar::Value
            } else {
                v
            }
        });
    }
}
