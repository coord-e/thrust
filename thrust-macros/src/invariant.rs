//! Expansion of `thrust_macros::invariant!` and its context-carrying sibling
//! `thrust_macros::_invariant_with_context!`.
//!
//! Both expand a predicate closure with explicit parameter types into a
//! `#[thrust::formula_fn]` over `Model::Ty` parameters plus a marker call
//! referencing it; they share [`expand_invariant`] and differ only in input:
//!
//! - `invariant!(|x: i64| x >= 1)` takes a bare predicate closure and only sees
//!   concrete types.
//! - `_invariant_with_context!(..)` additionally carries the enclosing generic
//!   context. It is never written by hand: `#[thrust_macros::invariant_context]`
//!   rewrites each `invariant!` it finds into this form, pasting the host
//!   function's signature (and, in methods, a `#[thrust::_outer_context(..)]`
//!   attribute carrying the enclosing `impl`/`trait` header) ahead of the
//!   closure:
//!
//!   ```ignore
//!   _invariant_with_context!(
//!       #[thrust::_outer_context(impl<T> Foo<T> where ..)]  // methods only
//!       fn f<U>(..) -> .. where ..;                         // host signature, as-is
//!       |x: T, v: T| x == v
//!   )
//!   ```
//!
//!   The in-scope generics (shadowing the enclosing ones) are re-declared on the
//!   formula function and instantiated via turbofish; in methods, `Self` is
//!   re-declared as a synthetic type parameter and instantiated with the real
//!   `Self` (legal in expression position).

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    visit_mut::VisitMut,
    FnArg, GenericParam, Signature, WherePredicate,
};

use crate::fn_outer_item::FnOuterItem;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Expands `invariant!(CLOSURE)`: a bare predicate closure with no threaded
/// context.
pub fn expand(input: TokenStream) -> TokenStream {
    let closure = parse_macro_input!(input as syn::ExprClosure);
    match expand_invariant(&closure, None) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// Expands `_invariant_with_context!(#outer_attr #sig; CLOSURE)`, the form
/// `#[thrust_macros::invariant_context]` rewrites each `invariant!` into.
pub fn expand_with_context(input: TokenStream) -> TokenStream {
    struct WithContext {
        context: Context,
        closure: syn::ExprClosure,
    }

    impl Parse for WithContext {
        fn parse(input: ParseStream) -> syn::Result<Self> {
            let attrs = input.call(syn::Attribute::parse_outer)?;
            let outer = crate::extract_outer_context(&attrs)?;
            let sig: Signature = input.parse()?;
            input.parse::<syn::Token![;]>()?;
            let closure: syn::ExprClosure = input.parse()?;
            Ok(Self {
                context: Context { sig, outer },
                closure,
            })
        }
    }

    let WithContext { closure, context } = parse_macro_input!(input as WithContext);
    match expand_invariant(&closure, Some(&context)) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// The enclosing context threaded into an invariant by
/// `#[thrust_macros::invariant_context]`: the host function signature and, for a
/// method, its `impl`/`trait` header. A standalone `invariant!` has none.
struct Context {
    sig: Signature,
    outer: Option<FnOuterItem>,
}

impl Context {
    /// The generic params in scope: the host signature's own, plus the outer
    /// `impl`/`trait`'s for a method.
    fn generic_params(&self) -> impl Iterator<Item = &GenericParam> {
        self.sig
            .generics
            .params
            .iter()
            .chain(self.outer.iter().flat_map(|o| o.generics().params.iter()))
    }

    /// The where-predicates in scope, from the host signature and (for a method)
    /// the outer `impl`/`trait`.
    fn where_predicates(&self) -> impl Iterator<Item = &WherePredicate> {
        fn preds(g: &syn::Generics) -> impl Iterator<Item = &WherePredicate> {
            g.where_clause.iter().flat_map(|wc| wc.predicates.iter())
        }
        preds(&self.sig.generics).chain(self.outer.iter().flat_map(|o| preds(o.generics())))
    }
}

/// Expands a predicate closure into a `#[thrust::formula_fn]` plus a marker
/// call. With `context`, the in-scope generics (and, in methods, `Self`) are
/// re-declared on the formula function and instantiated via turbofish.
fn expand_invariant(
    closure: &syn::ExprClosure,
    context: Option<&Context>,
) -> syn::Result<syn::Expr> {
    let mut fn_params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "invariant closure parameters must have explicit types, e.g. `|x: i64| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        fn_params.push(syn::parse_quote!(#pat: #ty));
    }

    let mut def_params: Vec<TokenStream2> = Vec::new();
    let mut turbofish_args: Vec<TokenStream2> = Vec::new();
    for param in context.into_iter().flat_map(Context::generic_params) {
        def_params.push(param.to_token_stream());
        match param {
            GenericParam::Type(tp) => turbofish_args.push(tp.ident.to_token_stream()),
            GenericParam::Const(cp) => turbofish_args.push(cp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => {}
        }
    }

    let mut def_wheres: Vec<WherePredicate> = context
        .into_iter()
        .flat_map(Context::where_predicates)
        .cloned()
        .collect();
    if let Some(context) = context {
        def_wheres.extend(crate::model_where_predicates(
            &context.sig,
            context.outer.as_ref(),
        ));
    }

    // `Self` in a method context: rewrite it to a synthetic generic, then pass
    // the real `Self` via turbofish (legal in expression position).
    if crate::tokens_contain_ident(&closure.to_token_stream(), "Self") {
        let synth: syn::Ident = format_ident!("__ThrustSelf");
        for param in &mut fn_params {
            SelfRewriter { synth: &synth }.visit_fn_arg_mut(param);
        }
        def_params.push(quote!(#synth));
        def_wheres.extend(crate::model_predicates(&synth));
        turbofish_args.push(quote!(Self));
    }

    let model_ty_params = crate::fn_params_with_model_ty(&fn_params);
    let body = &closure.body;

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);
    let name = format_ident!("_thrust_invariant_{}", id);

    let def_generics = if def_params.is_empty() {
        quote!()
    } else {
        quote!(<#(#def_params),*>)
    };
    let where_clause = if def_wheres.is_empty() {
        quote!()
    } else {
        quote!(where #(#def_wheres),*)
    };
    let turbofish = if turbofish_args.is_empty() {
        quote!()
    } else {
        quote!(::<#(#turbofish_args),*>)
    };

    Ok(syn::parse_quote!({
        #[allow(unused_variables)]
        #[allow(non_snake_case)]
        #[thrust::formula_fn]
        fn #name #def_generics(#model_ty_params) -> bool #where_clause {
            #body
        }

        thrust_models::__invariant_marker(#name #turbofish)
    }))
}

struct SelfRewriter<'a> {
    synth: &'a syn::Ident,
}

impl VisitMut for SelfRewriter<'_> {
    fn visit_path_mut(&mut self, path: &mut syn::Path) {
        syn::visit_mut::visit_path_mut(self, path);
        if path.leading_colon.is_none()
            && path.segments.len() == 1
            && path.segments[0].ident == "Self"
        {
            path.segments[0].ident = self.synth.clone();
        }
    }
}
