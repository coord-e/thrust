//! Expansion of `thrust_macros::ghost!` and its context-carrying sibling
//! `thrust_macros::_ghost_with_context!` into a `#[thrust::formula_fn]` relating the
//! introduced value to the ghost term, plus a marker call the analyzer intercepts.
//!
//! The value is parameter `0`, as in an `ensures` formula function: that is the layout
//! the analyzer reads the term back with. Unlike `ensures`, it is bound to a synthetic
//! name, leaving `result` free for a term to name a live variable with.
//!
//! `ghost!(|x: i64| -> Seq<Int> { .. })` only sees concrete types.
//! `_ghost_with_context!(..)` additionally carries the enclosing generic context (see
//! [`mod@crate::formula_fn_lifting`]), so a term may name generic- and `Self`-typed
//! variables; `#[thrust_macros::context]` rewrites each `ghost!` it finds into
//! that form.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, ToTokens};
use syn::FnArg;

use crate::formula_fn_lifting::{self, ClosureWithContext, EnclosingContext, LiftedFormulaFn};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Expands `ghost!(CLOSURE)`: a bare ghost term with no threaded context.
pub fn expand(input: TokenStream) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let closure = match syn::parse2::<syn::ExprClosure>(input) {
        Ok(closure) => closure,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_ghost(&closure, None) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands `_ghost_with_context!(#outer_attr #sig; CLOSURE)`, the form
/// `#[thrust_macros::context]` rewrites each `ghost!` into.
pub fn expand_with_context(input: TokenStream) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let ClosureWithContext { closure, context } = match syn::parse2::<ClosureWithContext>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_ghost(&closure, Some(&context)) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand_ghost(
    closure: &syn::ExprClosure,
    context: Option<&EnclosingContext>,
) -> syn::Result<syn::Expr> {
    let syn::ReturnType::Type(_, value_ty) = &closure.output else {
        return Err(syn::Error::new_spanned(
            closure,
            "ghost expression must have an explicit type, e.g. `|x: i64| -> Seq<Int> { .. }`",
        ));
    };

    // Synthetic, so that a term may name a live variable called `result`.
    let value = format_ident!("__thrust_ghost_value");
    let mut params: Vec<FnArg> = vec![syn::parse_quote!(#value: #value_ty)];
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "ghost expression parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        params.push(syn::parse_quote!(#pat: #ty));
    }

    let term = &closure.body;
    let body = syn::parse_quote!(#value == (#term));

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("_thrust_ghost_{}", id);
    let LiftedFormulaFn { item, reference } =
        formula_fn_lifting::lift(&name, &params, &body, context)?;

    Ok(syn::parse_quote!({
        #item

        crate::thrust_models::__ghost_marker::<_, #value_ty>(#reference)
    }))
}
