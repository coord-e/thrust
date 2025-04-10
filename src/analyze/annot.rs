use rustc_ast::ast::Attribute;
use rustc_ast::tokenstream::TokenStream;
use rustc_index::IndexVec;
use rustc_middle::ty as mir_ty;
use rustc_span::symbol::{Ident, Symbol};

use crate::annot;
use crate::rty;

pub fn requires_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("requires")]
}

pub fn ensures_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("ensures")]
}

pub fn param_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("param")]
}

pub fn ret_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("ret")]
}

pub fn trusted_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("trusted")]
}

pub fn callable_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("callable")]
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
    type Output = rty::FunctionParamIdx;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, annot::TermKind)> {
        self.params
            .iter_enumerated()
            .find(|(_, (name, _))| name == &ident.name)
            .map(|(idx, (_, kind))| (idx, kind.clone()))
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
        let result_kind = ty_to_term_kind(result_ty);
        Self {
            result_symbol,
            result_kind,
        }
    }
}

pub fn extract_annot_tokens(attr: Attribute) -> TokenStream {
    use rustc_ast::{AttrArgs, AttrKind, DelimArgs};

    let AttrKind::Normal(attr) = &attr.kind else {
        panic!("invalid attribute");
    };

    let AttrArgs::Delimited(DelimArgs { tokens, .. }, ..) = &attr.item.args else {
        panic!("invalid attribute");
    };

    tokens.clone()
}

pub fn split_param(ts: &TokenStream) -> (Ident, TokenStream) {
    use rustc_ast::token::TokenKind;
    use rustc_ast::tokenstream::TokenTree;

    let mut cursor = ts.trees();
    let (ident, _) = match cursor.next() {
        Some(TokenTree::Token(t, _)) => t.ident().expect("expected parameter name"),
        _ => panic!("expected parameter name"),
    };
    match cursor.next() {
        Some(TokenTree::Token(t, _)) if t.kind == TokenKind::Colon => {}
        _ => panic!("expected :"),
    }
    (ident, cursor.cloned().collect())
}
