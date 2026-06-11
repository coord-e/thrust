//! Supporting implementation for parsing Thrust annotations.

use rustc_ast::tokenstream::TokenStream;
use rustc_hir::Attribute;
use rustc_span::symbol::Symbol;

use crate::rty;

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

pub fn invariant_marker_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("invariant_marker"),
    ]
}

pub fn closure_precondition_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("closure_precondition"),
    ]
}

pub fn closure_postcondition_path() -> [Symbol; 3] {
    [
        Symbol::intern("thrust"),
        Symbol::intern("def"),
        Symbol::intern("closure_postcondition"),
    ]
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
/// Tokens are comma-separated [`rty::TypePositionStep`]s, each encoded as
/// `result` (→ `Return`), `$i` (→ `Param(i)`), or a bare integer `i` (→
/// `TypeArg(i)`).
pub fn parse_type_position(ts: &TokenStream) -> rty::TypePosition {
    use rustc_ast::token::{LitKind, TokenKind};
    use rustc_ast::tokenstream::TokenTree;

    let parse_int = |lit: &rustc_ast::token::Lit| -> usize {
        assert_eq!(
            lit.kind,
            LitKind::Integer,
            "expected an integer in type position"
        );
        lit.symbol
            .as_str()
            .parse()
            .expect("invalid integer in type position")
    };

    let mut steps = Vec::new();
    let mut iter = ts.iter();
    while let Some(tt) = iter.next() {
        let TokenTree::Token(t, _) = tt else {
            panic!("unexpected token tree in type position");
        };
        match &t.kind {
            TokenKind::Comma => {}
            TokenKind::Ident(sym, _) if sym.as_str() == "result" => {
                steps.push(rty::TypePositionStep::Return);
            }
            TokenKind::Dollar => {
                let i = match iter.next() {
                    Some(TokenTree::Token(t, _)) => match &t.kind {
                        TokenKind::Literal(lit) => parse_int(lit),
                        _ => panic!("expected integer after `$` in type position: {:?}", t),
                    },
                    _ => panic!("expected integer after `$` in type position"),
                };
                steps.push(rty::TypePositionStep::Param(rty::FunctionParamIdx::from(i)));
            }
            TokenKind::Literal(lit) => {
                steps.push(rty::TypePositionStep::TypeArg(parse_int(lit)));
            }
            _ => panic!("unexpected token in type position: {:?}", t),
        }
    }

    rty::TypePosition::new(steps)
}
