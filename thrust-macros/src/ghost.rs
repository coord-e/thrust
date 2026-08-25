//! Expansion of `thrust_macros::ghost!` into a `#[thrust::formula_fn]` relating the
//! introduced value to the ghost term, plus a marker call the analyzer intercepts.
//!
//! The value is parameter `0`, as in an `ensures` formula function: that is the layout
//! the analyzer reads the term back with. Unlike `ensures`, it is bound to a synthetic
//! name, leaving `result` free for a term to name a live variable with.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, ToTokens};
use syn::FnArg;

use crate::FormulaFnTypeLowering;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn expand(input: TokenStream) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let closure = match syn::parse2::<syn::ExprClosure>(input) {
        Ok(closure) => closure,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_ghost(&closure) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand_ghost(closure: &syn::ExprClosure) -> syn::Result<syn::Expr> {
    let syn::ReturnType::Type(_, value_ty) = &closure.output else {
        return Err(syn::Error::new_spanned(
            closure,
            "ghost expression must have an explicit type, e.g. `|x: i64| -> Seq<Int> { .. }`",
        ));
    };

    // Synthetic, so that a term may name a live variable called `result`.
    let value = format_ident!("__thrust_ghost_value");
    let mut fn_params: Vec<FnArg> = vec![syn::parse_quote!(#value: #value_ty)];
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "ghost expression parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        fn_params.push(syn::parse_quote!(#pat: #ty));
    }

    let dummy_sig = syn::parse_quote!(fn f());
    let model_ty_params = FormulaFnTypeLowering::new(&dummy_sig).lower_params(&fn_params);

    let body = &closure.body;
    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("_thrust_ghost_{}", id);

    Ok(syn::parse_quote!({
        #[thrust::formula_fn]
        fn #name(#model_ty_params) -> bool {
            #value == (#body)
        }

        thrust_models::__ghost_marker::<_, #value_ty>(#name)
    }))
}
