use rustc_index::IndexVec;
use rustc_middle::ty as mir_ty;
use rustc_span::symbol::{Ident, Symbol};

use crate::annot;
use crate::rty;

pub fn requires_path() -> [Symbol; 2] {
    [Symbol::intern("refa"), Symbol::intern("requires")]
}

pub fn ensures_path() -> [Symbol; 2] {
    [Symbol::intern("refa"), Symbol::intern("ensures")]
}

fn ty_to_term_kind(ty: &mir_ty::Ty<'_>) -> annot::TermKind {
    match ty.kind() {
        mir_ty::TyKind::Ref(_, ty, mir_ty::Mutability::Mut) => {
            annot::TermKind::mut_(ty_to_term_kind(ty))
        }
        mir_ty::TyKind::Ref(_, ty, mir_ty::Mutability::Not) => {
            annot::TermKind::box_(ty_to_term_kind(ty))
        }
        mir_ty::TyKind::Adt(def, _) if def.is_box() => annot::TermKind::box_(ty_to_term_kind(ty)),
        _ => annot::TermKind::other(),
    }
}

#[derive(Debug, Clone, Default)]
pub struct ParamResolver {
    params: IndexVec<rty::FunctionParamIdx, (Symbol, annot::TermKind)>,
}

impl annot::Resolver for ParamResolver {
    type Output = rty::RefinedTypeVar<rty::FunctionParamIdx>;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, annot::TermKind)> {
        self.params
            .iter_enumerated()
            .find(|(_, (name, _))| name == &ident.name)
            .map(|(idx, (_, kind))| (rty::RefinedTypeVar::Free(idx), kind.clone()))
    }
}

impl ParamResolver {
    pub fn push_param(&mut self, name: Symbol, ty: &mir_ty::Ty<'_>) {
        self.params.push((name, ty_to_term_kind(ty)));
    }
}

#[derive(Debug, Clone)]
pub struct ResultResolver {
    result_symbol: Symbol,
    result_kind: annot::TermKind,
}

impl annot::Resolver for ResultResolver {
    type Output = rty::RefinedTypeVar<rty::FunctionParamIdx>;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, annot::TermKind)> {
        if ident.name == self.result_symbol {
            Some((rty::RefinedTypeVar::Value, self.result_kind.clone()))
        } else {
            None
        }
    }
}

impl ResultResolver {
    pub fn new(result_ty: &mir_ty::Ty<'_>) -> Self {
        let result_symbol = Symbol::intern("result");
        let result_kind = ty_to_term_kind(&result_ty);
        Self {
            result_symbol,
            result_kind,
        }
    }
}
