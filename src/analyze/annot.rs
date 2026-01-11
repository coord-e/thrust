//! Supporting implementation for parsing Thrust annotations.

use rustc_ast::ast::Attribute;
use rustc_ast::tokenstream::TokenStream;
use rustc_index::IndexVec;
use rustc_span::symbol::{Ident, Symbol};

use crate::annot;
use crate::chc;
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

pub fn extern_spec_fn_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("extern_spec_fn")]
}

pub fn raw_define_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("raw_define")]
}

/// A [`annot::Resolver`] implementation for resolving function parameters.
///
/// The parameter names and their sorts needs to be configured via
/// [`ParamResolver::push_param`] before use.
#[derive(Debug, Clone, Default)]
pub struct ParamResolver {
    params: IndexVec<rty::FunctionParamIdx, (Symbol, chc::Sort)>,
}

impl annot::Resolver for ParamResolver {
    type Output = rty::FunctionParamIdx;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
        self.params
            .iter_enumerated()
            .find(|(_, (name, _))| name == &ident.name)
            .map(|(idx, (_, sort))| (idx, sort.clone()))
    }
}

impl ParamResolver {
    pub fn push_param(&mut self, name: Symbol, sort: chc::Sort) {
        self.params.push((name, sort));
    }
}

/// A [`annot::Resolver`] implementation for resolving the special identifier `result`.
///
/// The `result` identifier is used to refer to [`rty::RefinedTypeVar::Value`] in postconditions, denoting
/// the return value of a function.
#[derive(Debug, Clone)]
pub struct ResultResolver {
    result_symbol: Symbol,
    result_sort: chc::Sort,
}

impl annot::Resolver for ResultResolver {
    type Output = rty::RefinedTypeVar<rty::FunctionParamIdx>;
    fn resolve(&self, ident: Ident) -> Option<(Self::Output, chc::Sort)> {
        if ident.name == self.result_symbol {
            Some((rty::RefinedTypeVar::Value, self.result_sort.clone()))
        } else {
            None
        }
    }
}

impl ResultResolver {
    pub fn new(result_sort: chc::Sort) -> Self {
        let result_symbol = Symbol::intern("result");
        Self {
            result_symbol,
            result_sort,
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
