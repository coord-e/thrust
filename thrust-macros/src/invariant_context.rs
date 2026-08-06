//! Expansion of `#[thrust_macros::invariant_context]`.
//!
//! Threads the surrounding generic context (and, in methods, `Self`) into every
//! `thrust_macros::invariant!(...)` and `thrust_macros::proof_assert!(...)` call
//! inside the annotated function, so their predicates may refer to generic- and
//! `Self`-typed variables that the standalone macros cannot see.
//!
//! It also extends the host function's where clause with the `Model` predicates for every in-scope
//! type parameter (and for `Self` when used), since each injected marker call instantiates a
//! `Model`-bounded formula function with the host's own generics.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens};
use syn::{visit_mut::VisitMut, Signature};

use crate::fn_outer_item::FnOuterItem;

pub fn expand(item: TokenStream) -> TokenStream {
    let mut item_fn = syn::parse_macro_input!(item as syn::ItemFn);

    let outer = match crate::extract_outer_context(&item_fn.attrs) {
        Ok(outer) => outer,
        Err(e) => return e.to_compile_error().into(),
    };

    let sig = item_fn.sig.clone();
    let mut injector = ContextInjector {
        sig: &sig,
        outer: outer.as_ref(),
        self_used: false,
    };
    injector.visit_block_mut(&mut item_fn.block);

    let type_lowering = if let Some(outer) = &outer {
        crate::FormulaFnTypeLowering::with_outer_context(&sig, outer)
    } else {
        crate::FormulaFnTypeLowering::new(&sig)
    };
    let mut predicates = type_lowering.model_where_predicates();
    if injector.self_used {
        predicates.extend(type_lowering.model_where_predicates_for(&quote::format_ident!("Self")));
    }
    if !predicates.is_empty() {
        item_fn
            .sig
            .generics
            .make_where_clause()
            .predicates
            .extend(predicates);
    }

    item_fn.into_token_stream().into()
}

struct ContextInjector<'a> {
    sig: &'a Signature,
    outer: Option<&'a FnOuterItem>,
    self_used: bool,
}

impl<'a> ContextInjector<'a> {
    fn inject_context(&self, closure: &TokenStream2) -> TokenStream2 {
        let sig = self.sig;
        let outer_attr = self
            .outer
            .map(|outer| quote!(#[thrust::_outer_context(#outer)]));

        quote! {
            #outer_attr
            #sig;
            #closure
        }
    }
}

impl VisitMut for ContextInjector<'_> {
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        let Some(with_context) = with_context_macro_of(&mac.path) else {
            return;
        };
        if crate::tokens_contain_ident(&mac.tokens, "Self") {
            self.self_used = true;
        }
        mac.tokens = self.inject_context(&mac.tokens);
        mac.path = with_context;
    }
}

/// The context-carrying counterpart of the predicate-closure macro `path`
/// names, or `None` if it names some other macro.
fn with_context_macro_of(path: &syn::Path) -> Option<syn::Path> {
    // TODO: identify the macro precisely
    let ident = &path.segments.last()?.ident;
    if ident == "invariant" {
        Some(syn::parse_quote!(::thrust_macros::_invariant_with_context))
    } else if ident == "proof_assert" {
        Some(syn::parse_quote!(
            ::thrust_macros::_proof_assert_with_context
        ))
    } else {
        None
    }
}
