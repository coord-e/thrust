//! Expansion of `thrust_macros::invariant!`.
//!
//! Expands a closure with concrete parameter types into a
//! `#[thrust::formula_fn]` over `Model::Ty` parameters and a marker call
//! referencing it.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::{parse_macro_input, FnArg};

use crate::fn_params_with_model_ty;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn expand(input: TokenStream) -> TokenStream {
    let closure = parse_macro_input!(input as syn::ExprClosure);

    let mut fn_params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return syn::Error::new_spanned(
                param,
                "invariant closure parameters must have explicit types, e.g. `|x: i64| ...`",
            )
            .to_compile_error()
            .into();
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        fn_params.push(syn::parse_quote!(#pat: #ty));
    }

    let model_ty_params = fn_params_with_model_ty(&fn_params);
    let body = &closure.body;

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("_thrust_invariant_{}", id);

    quote! {
        {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #name(#model_ty_params) -> bool {
                #body
            }

            thrust_models::__invariant_marker(#name)
        }
    }
    .into()
}
