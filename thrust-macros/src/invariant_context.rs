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
//! context, by rewriting each `invariant!(..)` call into a
//! `thrust_macros::_invariant_with_context!(..)` call carrying that context (a
//! `fn` header carrying the in-scope generics/where clause, plus a
//! `#[thrust::_outer_context(..)]` attribute carrying the enclosing
//! `impl`/`trait` header for methods).
//!
//! It also extends the host function's where clause with `T: Model` and
//! `<T as Model>::Ty: PartialEq` predicates for every in-scope type parameter
//! (and for `Self` when used), since each injected marker call instantiates a
//! `Model`-bounded formula function with the host's own generics.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree};
use quote::{quote, ToTokens};
use syn::{visit_mut::VisitMut, GenericParam, Generics};

use crate::FnOuterItem;

pub(super) fn expand(item: TokenStream) -> TokenStream {
    let mut item_fn = syn::parse_macro_input!(item as syn::ItemFn);

    let outer = match crate::extract_outer_context(&item_fn.attrs) {
        Ok(outer) => outer,
        Err(e) => return e.to_compile_error().into(),
    };

    let generics = item_fn.sig.generics.clone();
    let mut injector = InvariantInjector::new(&generics, outer.as_ref());
    injector.visit_block_mut(&mut item_fn.block);
    injector.inject_model_bounds(&mut item_fn.sig.generics);

    item_fn.into_token_stream().into()
}

struct InvariantInjector<'a> {
    /// The enclosing function's own generics.
    fn_generics: &'a Generics,
    /// The enclosing `impl`/`trait` header, for a method.
    outer: Option<&'a FnOuterItem>,
    /// Whether any rewritten invariant references `Self`.
    self_used: bool,
}

impl<'a> InvariantInjector<'a> {
    fn new(fn_generics: &'a Generics, outer: Option<&'a FnOuterItem>) -> Self {
        Self {
            fn_generics,
            outer,
            self_used: false,
        }
    }

    /// Builds the context-carrying argument for `_invariant_with_context!` from
    /// the closure inside an `invariant!(CLOSURE)` call: a `fn` header carrying
    /// the in-scope generics/where clause, tagged (for methods) with the
    /// enclosing `impl`/`trait` header.
    fn inject_context(&self, closure: &TokenStream2) -> TokenStream2 {
        let generics = self.fn_generics;
        let where_clause = &self.fn_generics.where_clause;
        let outer_attr = self
            .outer
            .map(|outer| quote!(#[thrust::_outer_context(#outer)]));

        quote! {
            #outer_attr
            fn _thrust_invariant_context #generics () #where_clause {
                #closure
            }
        }
    }

    /// Adds `T: Model` and `<T as Model>::Ty: PartialEq` bounds for every type
    /// parameter in scope (the host function's own, the outer `impl`/`trait`'s,
    /// and `Self` when an invariant names it) to the host's where clause.
    fn inject_model_bounds(&self, generics: &mut Generics) {
        let mut tys: Vec<TokenStream2> = type_param_idents(self.fn_generics);
        if let Some(outer) = self.outer {
            tys.extend(type_param_idents(outer.generics()));
        }
        if self.self_used {
            tys.push(quote!(Self));
        }
        if tys.is_empty() {
            return;
        }
        let where_clause = generics.make_where_clause();
        for ty in tys {
            where_clause.predicates.extend(crate::model_predicates(&ty));
        }
    }
}

impl VisitMut for InvariantInjector<'_> {
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

fn type_param_idents(generics: &Generics) -> Vec<TokenStream2> {
    generics
        .params
        .iter()
        .filter_map(|p| match p {
            GenericParam::Type(tp) => Some(tp.ident.to_token_stream()),
            _ => None,
        })
        .collect()
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
