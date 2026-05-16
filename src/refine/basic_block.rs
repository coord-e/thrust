//! The refinement type for a basic block.

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
}
