//! Expansion of `thrust_macros::invariant!`.
//!
//! Expands a predicate closure with explicit parameter types into a
//! `#[thrust::formula_fn]` over `Model::Ty` parameters plus a marker call
//! referencing it.
//!
//! A standalone `invariant!(|x: i64| x >= 1)` only sees concrete types. To
//! refer to generic- or `Self`-typed variables, the enclosing item must be
//! annotated with `#[thrust_macros::invariant_context]`, which rewrites each
//! call into a context-carrying form that threads the in-scope generics (and,
//! in methods, `Self`) into the macro input:
//!
//! ```ignore
//! invariant!(
//!     #[thrust::_outer_context(impl<T> Foo<T> where ..)]  // methods only
//!     fn _ctx<U>() where .. {
//!         |x: T, v: T| x == v
//!     }
//! )
//! ```
//!
//! This macro re-declares the threaded generics (shadowing the enclosing ones)
//! on the formula function and instantiates it via turbofish; in methods,
//! `Self` is re-declared as a synthetic type parameter and instantiated with
//! the real `Self` (legal in expression position).

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input,
    visit_mut::VisitMut,
    FnArg, GenericParam, WherePredicate,
};

use crate::FnOuterItem;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

pub fn expand(input: TokenStream) -> TokenStream {
    let invariant = parse_macro_input!(input as Invariant);
    invariant.expand().into_token_stream().into()
}

/// The parsed `invariant!` input: the predicate closure plus the enclosing
/// generic context threaded in by `#[thrust_macros::invariant_context]`.
struct Invariant {
    closure: syn::ExprClosure,
    /// In-scope generic params (the enclosing function's own, plus the outer
    /// `impl`/`trait`'s for a method). Empty for a standalone `invariant!`.
    params: Vec<GenericParam>,
    /// Combined where-predicates from the function and (for a method) the
    /// outer `impl`/`trait`.
    wheres: Vec<WherePredicate>,
    /// Whether `Self` is nameable at the call site (i.e. we are in a method).
    is_method: bool,
}

impl Parse for Invariant {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // Context-carrying form injected by `invariant_context`: a function
        // header whose generics/where clause carry the enclosing context and
        // whose body is the predicate closure. It always starts with the
        // `#[thrust::_outer_context(..)]` attribute (methods) or `fn` (free
        // functions); a standalone predicate closure starts with neither.
        if input.peek(syn::Token![#]) || input.peek(syn::Token![fn]) {
            let ctx_fn: syn::ItemFn = input.parse()?;
            return Self::from_context_fn(ctx_fn);
        }

        Ok(Self {
            closure: input.parse()?,
            params: Vec::new(),
            wheres: Vec::new(),
            is_method: false,
        })
    }
}

impl Invariant {
    fn from_context_fn(ctx_fn: syn::ItemFn) -> syn::Result<Self> {
        let outer = extract_outer_context(&ctx_fn.attrs)?;

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

        Ok(Self {
            closure,
            params,
            wheres,
            is_method: outer.is_some(),
        })
    }

    fn expand(&self) -> syn::Expr {
        let mut fn_params: Vec<FnArg> = Vec::new();
        for param in &self.closure.inputs {
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
        let mut def_wheres: Vec<TokenStream2> =
            self.wheres.iter().map(|w| w.to_token_stream()).collect();
        let mut turbofish_args: Vec<TokenStream2> = Vec::new();

        // `Self` in a method context: rewrite it to a synthetic generic, then
        // pass the real `Self` via turbofish (legal in expression position).
        let uses_self = self.is_method && tokens_contain_self(&self.closure.to_token_stream());
        if uses_self {
            let synth: syn::Ident = format_ident!("__ThrustSelf");
            for param in &mut fn_params {
                SelfRewriter { synth: &synth }.visit_fn_arg_mut(param);
            }
            def_params.push(quote!(#synth));
            def_wheres.push(quote!(#synth: thrust_models::Model));
            def_wheres.push(quote!(<#synth as thrust_models::Model>::Ty: PartialEq));
            turbofish_args.push(quote!(Self));
        }

        for param in &self.params {
            def_params.push(param.to_token_stream());
            match param {
                GenericParam::Type(tp) => {
                    let ident = &tp.ident;
                    def_wheres.push(quote!(#ident: thrust_models::Model));
                    def_wheres.push(quote!(<#ident as thrust_models::Model>::Ty: PartialEq));
                    turbofish_args.push(ident.to_token_stream());
                }
                GenericParam::Const(cp) => turbofish_args.push(cp.ident.to_token_stream()),
                GenericParam::Lifetime(_) => {}
            }
        }

        let model_ty_params = crate::fn_params_with_model_ty(&fn_params);
        let body = &self.closure.body;

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
}

/// Reads the optional `#[thrust::_outer_context(..)]` attribute threaded onto a
/// context-carrying invariant by `invariant_context`.
fn extract_outer_context(attrs: &[syn::Attribute]) -> syn::Result<Option<FnOuterItem>> {
    let outer_context_path: syn::Path = syn::parse_quote!(thrust::_outer_context);
    let mut outer_context = None;
    for attr in attrs {
        if attr.path() != &outer_context_path {
            continue;
        }
        if outer_context.is_some() {
            return Err(syn::Error::new_spanned(
                attr,
                "multiple _outer_context attributes found; expected at most one",
            ));
        }
        outer_context = Some(attr.parse_args()?);
    }
    Ok(outer_context)
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
