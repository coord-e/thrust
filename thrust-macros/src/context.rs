//! Expansion of `#[thrust_macros::context]`.
//!
//! Makes the enclosing context available to the specifications written inside an item.
//!
//! On a function, every `thrust_macros::invariant!(...)` in the body is rewritten into
//! its context-carrying counterpart, carrying the host signature and, for a method, the
//! enclosing `impl`/`trait` header, so an invariant may refer to generic- and
//! `Self`-typed variables that the standalone macro cannot see. That also extends the
//! function's where clause with the `Model` predicates for every in-scope type parameter
//! (and for `Self` when used), since each injected marker call instantiates a
//! `Model`-bounded formula function with the host's own generics.
//!
//! On an `impl`/`trait`, each method is stamped with the enclosing header — which is what
//! method-level `requires`/`ensures` read to recover the outer generics — and with this
//! attribute, so a method's body is threaded by an expansion of its own.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens as _};
use syn::{
    parse::{Parse, ParseStream},
    visit_mut::VisitMut,
    Signature,
};

use crate::{fn_outer_item::FnOuterItem, spec::FnItemWithSignature};

pub fn expand(item: TokenStream) -> TokenStream {
    match syn::parse_macro_input!(item as ContextItem) {
        ContextItem::Fn(func) => expand_fn(func),
        ContextItem::Outer(outer_item) => expand_outer(outer_item),
    }
}

/// An item `#[thrust_macros::context]` applies to.
enum ContextItem {
    Fn(FnItemWithSignature),
    Outer(FnOuterItem),
}

impl Parse for ContextItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative as _;

        let fork = input.fork();
        if let Ok(func) = fork.parse::<FnItemWithSignature>() {
            input.advance_to(&fork);
            return Ok(Self::Fn(func));
        }

        input.parse().map(Self::Outer)
    }
}

/// Hands each method the enclosing header, and the attribute that puts it to use.
fn expand_outer(mut outer_item: FnOuterItem) -> TokenStream {
    let header = outer_item.clone().into_header_only();
    let method_attrs: [syn::Attribute; 2] = [
        syn::parse_quote!(#[thrust::_outer_context(#header)]),
        syn::parse_quote!(#[::thrust_macros::context]),
    ];
    match &mut outer_item {
        FnOuterItem::ItemImpl(item_impl) => {
            for item in &mut item_impl.items {
                let syn::ImplItem::Fn(item) = item else {
                    continue;
                };
                item.attrs.extend(method_attrs.clone());
            }
        }
        FnOuterItem::ItemTrait(item_trait) => {
            for item in &mut item_trait.items {
                let syn::TraitItem::Fn(item) = item else {
                    continue;
                };
                item.attrs.extend(method_attrs.clone());
            }
        }
    }
    outer_item.into_token_stream().into()
}

/// Rewrites each `invariant!` in the body into its context-carrying counterpart and
/// extends the where clause with the `Model` predicates those calls need. A body naming
/// no invariant — or a trait method that has no body at all — is left as it is.
fn expand_fn(mut func: FnItemWithSignature) -> TokenStream {
    let outer = match crate::extract_outer_context(func.attrs()) {
        Ok(outer) => outer,
        Err(e) => return e.to_compile_error().into(),
    };

    let host_sig = func.sig().clone();
    let mut injector = ContextInjector {
        sig: &host_sig,
        outer: outer.as_ref(),
        injected: false,
        self_used: false,
    };
    if let Some(body) = func.block_mut() {
        injector.visit_block_mut(body);
    }
    if !injector.injected {
        return func.into_token_stream().into();
    }

    let type_lowering = match &outer {
        Some(outer) => crate::FormulaFnTypeLowering::with_outer_context(&host_sig, outer),
        None => crate::FormulaFnTypeLowering::new(&host_sig),
    };
    let mut predicates = type_lowering.model_where_predicates();
    if injector.self_used {
        predicates.extend(type_lowering.model_where_predicates_for(&quote::format_ident!("Self")));
    }
    if !predicates.is_empty() {
        func.sig_mut()
            .generics
            .make_where_clause()
            .predicates
            .extend(predicates);
    }

    func.into_token_stream().into()
}

struct ContextInjector<'a> {
    sig: &'a Signature,
    outer: Option<&'a FnOuterItem>,
    injected: bool,
    self_used: bool,
}

impl ContextInjector<'_> {
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
        if !is_invariant_macro(&mac.path) {
            return;
        }
        self.injected = true;
        if crate::tokens_contain_ident(&mac.tokens, "Self") {
            self.self_used = true;
        }
        mac.tokens = self.inject_context(&mac.tokens);
        mac.path = syn::parse_quote!(::thrust_macros::_invariant_with_context);
    }
}

fn is_invariant_macro(path: &syn::Path) -> bool {
    // TODO: identify the macro precisely
    path.segments.last().is_some_and(|s| s.ident == "invariant")
}
