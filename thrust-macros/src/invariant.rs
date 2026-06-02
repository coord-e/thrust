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
//!   rewrites each `invariant!` it finds into this form, threading the in-scope
//!   generics (and, in methods, `Self`) in as an ordinary `fn` header whose body
//!   is the predicate closure:
//!
//!   ```ignore
//!   _invariant_with_context!(
//!       #[thrust::_outer_context(impl<T> Foo<T> where ..)]  // methods only
//!       fn _ctx<U>() where .. {
//!           |x: T, v: T| x == v
//!       }
//!   )
//!   ```
//!
//!   The threaded generics (shadowing the enclosing ones) are re-declared on the
//!   formula function and instantiated via turbofish; in methods, `Self` is
//!   re-declared as a synthetic type parameter and instantiated with the real
//!   `Self` (legal in expression position).

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, visit_mut::VisitMut, FnArg, GenericParam, WherePredicate};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Expands `invariant!(CLOSURE)`: a bare predicate closure with no threaded
/// context.
pub fn expand(input: TokenStream) -> TokenStream {
    let closure = parse_macro_input!(input as syn::ExprClosure);
    expand_invariant(&closure, None).into_token_stream().into()
}

/// Expands `_invariant_with_context!(CONTEXT_FN)`, the form
/// `#[thrust_macros::invariant_context]` rewrites each `invariant!` into.
pub fn expand_with_context(input: TokenStream) -> TokenStream {
    let ctx_fn = parse_macro_input!(input as syn::ItemFn);
    match Context::from_context_fn(ctx_fn) {
        Ok((closure, context)) => expand_invariant(&closure, Some(&context))
            .into_token_stream()
            .into(),
        Err(e) => e.to_compile_error().into(),
    }
}

/// The enclosing generic context threaded into an invariant by
/// `#[thrust_macros::invariant_context]`. A standalone `invariant!` has none.
struct Context {
    /// In-scope generic params: the enclosing function's own, plus the outer
    /// `impl`/`trait`'s for a method.
    params: Vec<GenericParam>,
    /// Combined where-predicates from the function and (for a method) the
    /// outer `impl`/`trait`.
    wheres: Vec<WherePredicate>,
    /// Whether `Self` is nameable at the call site (i.e. we are in a method).
    is_method: bool,
}

impl Context {
    /// Parses the `fn` header that carries the threaded context, returning the
    /// predicate closure from its body alongside the recovered context.
    fn from_context_fn(ctx_fn: syn::ItemFn) -> syn::Result<(syn::ExprClosure, Self)> {
        let outer = crate::extract_outer_context(&ctx_fn.attrs)?;

        let closure = match ctx_fn.block.stmts.as_slice() {
            [syn::Stmt::Expr(syn::Expr::Closure(closure), _)] => closure.clone(),
            _ => {
                return Err(syn::Error::new_spanned(
                    &ctx_fn.block,
                    "invariant context body must be a single predicate closure",
                ))
            }
        };

        let mut params: Vec<GenericParam> = ctx_fn.sig.generics.params.iter().cloned().collect();
        let mut wheres: Vec<WherePredicate> = ctx_fn
            .sig
            .generics
            .where_clause
            .as_ref()
            .map(|wc| wc.predicates.iter().cloned().collect())
            .unwrap_or_default();
        if let Some(outer) = &outer {
            params.extend(outer.generics().params.iter().cloned());
            if let Some(wc) = &outer.generics().where_clause {
                wheres.extend(wc.predicates.iter().cloned());
            }
        }

        Ok((
            closure,
            Self {
                params,
                wheres,
                is_method: outer.is_some(),
            },
        ))
    }
}

/// Expands a predicate closure into a `#[thrust::formula_fn]` plus a marker
/// call. With `context`, the threaded generics (and, in methods, `Self`) are
/// re-declared on the formula function and instantiated via turbofish.
fn expand_invariant(closure: &syn::ExprClosure, context: Option<&Context>) -> syn::Expr {
    let mut fn_params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            let err = syn::Error::new_spanned(
                param,
                "invariant closure parameters must have explicit types, e.g. `|x: i64| ...`",
            );
            return syn::Expr::Verbatim(err.to_compile_error());
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        fn_params.push(syn::parse_quote!(#pat: #ty));
    }

    let mut def_params: Vec<TokenStream2> = Vec::new();
    let mut def_wheres: Vec<WherePredicate> = context
        .iter()
        .flat_map(|ctx| ctx.wheres.iter())
        .cloned()
        .collect();
    let mut turbofish_args: Vec<TokenStream2> = Vec::new();

    // `Self` in a method context: rewrite it to a synthetic generic, then pass
    // the real `Self` via turbofish (legal in expression position).
    let uses_self =
        context.is_some_and(|ctx| ctx.is_method) && tokens_contain_self(&closure.to_token_stream());
    if uses_self {
        let synth: syn::Ident = format_ident!("__ThrustSelf");
        for param in &mut fn_params {
            SelfRewriter { synth: &synth }.visit_fn_arg_mut(param);
        }
        def_params.push(quote!(#synth));
        def_wheres.extend(crate::model_predicates(&synth));
        turbofish_args.push(quote!(Self));
    }

    for param in context.iter().flat_map(|ctx| ctx.params.iter()) {
        def_params.push(param.to_token_stream());
        match param {
            GenericParam::Type(tp) => {
                // A closure-typed param has no `Model` instance; re-declare and
                // pass it through, but do not bound it.
                if !crate::has_fn_bound(&tp.bounds) {
                    def_wheres.extend(crate::model_predicates(&tp.ident));
                }
                turbofish_args.push(tp.ident.to_token_stream());
            }
            GenericParam::Const(cp) => turbofish_args.push(cp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => {}
        }
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

    syn::parse_quote!({
        #[allow(unused_variables)]
        #[allow(non_snake_case)]
        #[thrust::formula_fn]
        fn #name #def_generics(#model_ty_params) -> bool #where_clause {
            #body
        }

        thrust_models::__invariant_marker(#name #turbofish)
    })
}

/// Rewrites a bare `Self` type path to a synthetic type parameter, so the type
/// can be named inside a nested formula function. Qualified paths such as
/// `Self::Assoc` are left untouched (and are not supported in invariants).
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

fn tokens_contain_self(tokens: &TokenStream2) -> bool {
    tokens.clone().into_iter().any(|tt| match tt {
        TokenTree::Ident(ident) => ident == "Self",
        TokenTree::Group(group) => tokens_contain_self(&group.stream()),
        _ => false,
    })
}
