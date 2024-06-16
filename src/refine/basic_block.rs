use pretty::{termcolor, Pretty};
use rustc_index::IndexVec;
use rustc_middle::mir::Local;
use rustc_middle::ty as mir_ty;

use crate::rty;

/// `BasicBlockType` is a special case of `FunctionType` whose parameters are
/// associated with `Local`s.
#[derive(Debug, Clone)]
pub struct BasicBlockType {
    // TODO: make this completely private by exposing appropriate ctor
    pub(super) ty: rty::FunctionType,
    pub(super) locals: IndexVec<rty::FunctionParamIdx, (Local, mir_ty::Mutability)>,
}

impl<'a, 'b, D> Pretty<'a, D, termcolor::ColorSpec> for &'b BasicBlockType
where
    D: pretty::DocAllocator<'a, termcolor::ColorSpec>,
    D::Doc: Clone,
{
    fn pretty(self, allocator: &'a D) -> pretty::DocBuilder<'a, D, termcolor::ColorSpec> {
        let separator = allocator.text(",").append(allocator.line());
        let params = self
            .ty
            .params
            .iter()
            .zip(&self.locals)
            .map(|(ty, (local, mutbl))| {
                allocator
                    .text(format!("{}{:?}:", mutbl.prefix_str(), local))
                    .append(allocator.space())
                    .append(ty.pretty(allocator))
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

    pub fn to_function_ty(&self) -> rty::FunctionType {
        self.ty.clone()
    }
}
