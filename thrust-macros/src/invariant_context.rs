//! Expansion of `#[thrust_macros::invariant_context]`.
//!
//! Threads the surrounding generic context (and, in methods, `Self`) into
//! every `thrust_macros::invariant!(...)` call inside the annotated function, so
//! an invariant may refer to generic- and `Self`-typed variables that the
//! standalone `invariant!` macro cannot see.
//!
//! It is applied to a single function. A method recovers its enclosing
//! `impl`/`trait` header from the `#[thrust::_outer_context(..)]` attribute
//! stamped by `#[thrust_macros::context]`, the same mechanism `requires`/
//! `ensures` use:
//!
//! ```ignore
//! #[thrust_macros::context]
//! impl<T> Foo<T> {
//!     #[thrust_macros::invariant_context]
//!     fn f(&self) { .. }
//! }
//! ```
//!
//! This macro does **not** expand the invariants itself: it only injects the
//! context, by rewriting each `invariant!(CLOSURE)` call into a
//! `thrust_macros::_invariant_with_context!(#outer_attr #signature; CLOSURE)`
//! call, pasting the host function's signature (and, for methods, a
//! `#[thrust::_outer_context(..)]` attribute carrying the enclosing
//! `impl`/`trait` header) so the expansion can recover the in-scope context.
//!
//! It also extends the host function's where clause with the `Model` predicates
//! (see [`crate::model_where_predicates`]) for every in-scope type parameter
//! (and for `Self` when used), since each injected marker call instantiates a
//! `Model`-bounded formula function with the host's own generics.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree};
use quote::{quote, ToTokens};
use syn::{visit_mut::VisitMut, Generics, Signature};

use crate::FnOuterItem;

pub(super) fn expand(item: TokenStream) -> TokenStream {
    let mut item_fn = syn::parse_macro_input!(item as syn::ItemFn);

    let outer = match crate::extract_outer_context(&item_fn.attrs) {
        Ok(outer) => outer,
        Err(e) => return e.to_compile_error().into(),
    };

    let sig = item_fn.sig.clone();
    let mut injector = ContextInjector::new(&sig, outer.as_ref());
    injector.visit_block_mut(&mut item_fn.block);
    injector.inject_model_bounds(&mut item_fn.sig.generics);

    item_fn.into_token_stream().into()
}

struct ContextInjector<'a> {
    /// The host function's signature, pasted verbatim into each rewritten call.
    sig: &'a Signature,
    /// The enclosing `impl`/`trait` header, for a method.
    outer: Option<&'a FnOuterItem>,
    /// Whether any rewritten invariant references `Self`.
    self_used: bool,
}

impl<'a> ContextInjector<'a> {
    fn new(sig: &'a Signature, outer: Option<&'a FnOuterItem>) -> Self {
        Self {
            sig,
            outer,
            self_used: false,
        }
    }

    /// Builds the context-carrying argument for `_invariant_with_context!` from
    /// the closure inside an `invariant!(CLOSURE)` call: the host signature
    /// pasted as-is, tagged (for methods) with the enclosing `impl`/`trait`
    /// header, followed by `; CLOSURE`.
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

    /// Extends the host where clause with the `Model` predicates for every
    /// in-scope type parameter (and for `Self` when an invariant names it), so
    /// the host can instantiate the `Model`-bounded formula functions.
    fn inject_model_bounds(&self, generics: &mut Generics) {
        let mut predicates = crate::model_where_predicates(self.sig, self.outer);
        if self.self_used {
            predicates.extend(crate::model_predicates(&quote!(Self)));
        }
        if predicates.is_empty() {
            return;
        }
        generics.make_where_clause().predicates.extend(predicates);
    }
}

impl VisitMut for ContextInjector<'_> {
    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if !is_invariant_macro(&mac.path) {
            return;
        }
        if self.outer.is_some() && tokens_contain_self(&mac.tokens) {
            self.self_used = true;
        }
        mac.tokens = self.inject_context(&mac.tokens);
        mac.path = syn::parse_quote!(::thrust_macros::_invariant_with_context);
    }
}

fn is_invariant_macro(path: &syn::Path) -> bool {
    path.segments.last().is_some_and(|s| s.ident == "invariant")
}

fn tokens_contain_self(tokens: &TokenStream2) -> bool {
    tokens.clone().into_iter().any(|tt| match tt {
        TokenTree::Ident(ident) => ident == "Self",
        TokenTree::Group(group) => tokens_contain_self(&group.stream()),
        _ => false,
    })
}
