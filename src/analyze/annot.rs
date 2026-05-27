//! Supporting implementation for parsing Thrust annotations.

use rustc_ast::tokenstream::TokenStream;
use rustc_hir::Attribute;
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

pub fn raw_command_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("raw_command")]
}

pub fn predicate_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("predicate")]
}

pub fn ignored_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("ignored")]
}

pub fn formula_fn_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("formula_fn")]
}

pub fn requires_path_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("requires_path")]
}

pub fn ensures_path_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("ensures_path")]
}

pub fn refinement_path_path() -> [Symbol; 2] {
    [Symbol::intern("thrust"), Symbol::intern("refinement_path")]
}

pub fn model_ty_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("model_ty"),
    ]
}

pub fn int_model_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("int_model"),
    ]
}

pub fn mut_model_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("mut_model"),
    ]
}

pub fn box_model_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("box_model"),
    ]
}

pub fn array_model_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("array_model"),
    ]
}

pub fn closure_model_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("closure_model"),
    ]
}

pub fn mut_model_new_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("mut_new"),
    ]
}

pub fn box_model_new_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("box_new"),
    ]
}

pub fn array_model_store_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("array_store"),
    ]
}

pub fn exists_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("exists"),
    ]
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
    let Attribute::Unparsed(item) = attr else {
        panic!("invalid attribute: expected unparsed");
    };
    let rustc_hir::AttrArgs::Delimited(d) = item.args else {
        panic!("invalid attribute: expected delimited args");
    };
    d.tokens
}

/// Parses a [`rty::TypePosition`] from the tokens of a
/// `#[thrust::refinement_path(..)]` attribute.
///
/// Tokens are comma-separated steps. Each step is one of:
/// - The keyword `result` → [`rty::TypePositionStep::Return`] (navigate to a
///   function type's return slot).
/// - An integer literal `i` → [`rty::TypePositionStep::Param`]`(i)` (navigate
///   to the `i`-th parameter of a function type).
/// - A bracket group `[i]` → [`rty::TypePositionStep::TypeArg`]`(i)` (navigate
///   to the `i`-th type argument of a generic type such as an enum or `Box`).
///
/// Examples: `result` is the return; `0` is the first parameter; `0, [0]` is
/// the first type-argument of the first parameter; `0, result` is the return of
/// a function-typed first parameter.
pub fn parse_type_position(ts: &TokenStream) -> rty::TypePosition {
    use rustc_ast::token::{Delimiter, LitKind, TokenKind};
    use rustc_ast::tokenstream::TokenTree;

    let parse_int = |lit: &rustc_ast::token::Lit| -> usize {
        assert_eq!(
            lit.kind,
            LitKind::Integer,
            "expected an integer in refine position"
        );
        lit.symbol
            .as_str()
            .parse()
            .expect("invalid integer in refine position")
    };

    let mut steps = Vec::new();
    for tt in ts.iter() {
        match tt {
            TokenTree::Token(t, _) => match &t.kind {
                TokenKind::Comma => {}
                TokenKind::Ident(sym, _) if sym.as_str() == "result" => {
                    steps.push(rty::TypePositionStep::Return);
                }
                TokenKind::Literal(lit) => {
                    steps.push(rty::TypePositionStep::Param(rty::FunctionParamIdx::from(
                        parse_int(lit),
                    )));
                }
                _ => panic!("unexpected token in refine position: {:?}", t),
            },
            TokenTree::Delimited(_, _, Delimiter::Bracket, inner) => {
                let mut inner_iter = inner.iter();
                let i = match inner_iter.next() {
                    Some(TokenTree::Token(t, _)) => match &t.kind {
                        TokenKind::Literal(lit) => parse_int(lit),
                        _ => panic!("expected integer inside [..] refine step: {:?}", t),
                    },
                    _ => panic!("expected integer inside [..] refine step"),
                };
                assert!(
                    inner_iter.next().is_none(),
                    "expected exactly one integer inside [..] refine step"
                );
                steps.push(rty::TypePositionStep::TypeArg(i));
            }
            _ => panic!("unexpected token tree in refine position"),
        }
    }

    assert!(!steps.is_empty(), "empty refine position");
    let first = steps.remove(0);
    rty::TypePosition::new(first, steps)
}

pub fn split_param(ts: &TokenStream) -> (Ident, TokenStream) {
    use rustc_ast::token::TokenKind;
    use rustc_ast::tokenstream::TokenTree;

    let mut iter = ts.iter();
    let (ident, _) = match iter.next() {
        Some(TokenTree::Token(t, _)) => t.ident().expect("expected parameter name"),
        _ => panic!("expected parameter name"),
    };
    match iter.next() {
        Some(TokenTree::Token(t, _)) if t.kind == TokenKind::Colon => {}
        _ => panic!("expected :"),
    }
    (ident, iter.cloned().collect())
}
