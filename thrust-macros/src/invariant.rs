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
    visit_mut::VisitMut,
    FnArg, GenericParam, Signature, WherePredicate,
};

use crate::{fn_outer_item::FnOuterItem, FormulaFnTypeLowering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

/// Expands `invariant!(CLOSURE)`: a bare predicate closure with no threaded
/// context.
pub fn expand(input: TokenStream) -> TokenStream {
    let input = crate::formula::wrap_closure_body(input.into());
    let closure = match syn::parse2::<syn::ExprClosure>(input) {
        Ok(closure) => closure,
        Err(e) => return e.to_compile_error().into(),
    };
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

    let input = crate::formula::wrap_closure_body(input.into());
    let WithContext { closure, context } = match syn::parse2::<WithContext>(input) {
        Ok(parsed) => parsed,
        Err(e) => return e.to_compile_error().into(),
    };
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

    fn type_lowering(&self) -> FormulaFnTypeLowering<'_> {
        if let Some(outer) = &self.outer {
            FormulaFnTypeLowering::with_outer_context(&self.sig, outer)
        } else {
            FormulaFnTypeLowering::new(&self.sig)
        }
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

    let dummy_sig = syn::parse_quote!(fn f());
    let type_lowering = if let Some(context) = context {
        context.type_lowering()
    } else {
        FormulaFnTypeLowering::new(&dummy_sig)
    };

    def_wheres.extend(type_lowering.model_where_predicates());

    let mut body = closure.body.clone();

    // An invariant may refer to the receiver value `self`; the lifted formula function is free, so
    // rewrite `self` to a `__thrust_self` parameter. The analyzer binds it back to the loop-carried receiver.
    let mut rewriter = SelfValueRewriter {
        to: format_ident!("__thrust_self"),
    };
    for param in &mut fn_params {
        rewriter.visit_fn_arg_mut(param);
    }
    rewriter.visit_expr_mut(&mut body);

    let self_used = crate::tokens_contain_ident(&closure.to_token_stream(), "Self")
        || def_wheres
            .iter()
            .any(|pred| crate::tokens_contain_ident(&pred.to_token_stream(), "Self"));
    if self_used {
        let Some(outer) = context.and_then(|context| context.outer.as_ref()) else {
            return Err(syn::Error::new_spanned(
                closure,
                "invariant closure cannot refer to `Self` without an enclosing impl/trait context",
            ));
        };

        match outer {
            FnOuterItem::ItemImpl(item_impl) => {
                // `Self` in an impl method context: rewrite it to the concrete self type everywhere
                // TODO: Support generic/trait impl
                let self_ty = &item_impl.self_ty;
                let mut rewriter = SelfTypeRewriter {
                    to: *self_ty.clone(),
                };
                for param in &mut fn_params {
                    rewriter.visit_fn_arg_mut(param);
                }
                rewriter.visit_expr_mut(&mut body);
                for pred in &mut def_wheres {
                    rewriter.visit_where_predicate_mut(pred);
                }
            }
            FnOuterItem::ItemTrait(item_trait) => {
                // `Self` in a trait method context: rewrite it to a synthetic generic everywhere
                // it reaches the formula function — parameters, body, and the propagated
                // where-clause predicates — then pass the real `Self` via turbofish (legal
                // in expression position).
                let synth: syn::Ident = format_ident!("__ThrustSelf");
                def_wheres.push(syn::parse_quote!(#synth: ?Sized));

                let mut rewriter = SelfTypeRewriter {
                    to: syn::parse_quote!(#synth),
                };
                for param in &mut fn_params {
                    rewriter.visit_fn_arg_mut(param);
                }
                rewriter.visit_expr_mut(&mut body);
                for pred in &mut def_wheres {
                    rewriter.visit_where_predicate_mut(pred);
                }
                def_params.push(quote!(#synth));
                def_wheres.extend(type_lowering.model_where_predicates_for(&synth));

                // Mirror the host's implicit `Self: Trait` bound onto the synthetic
                // generic so trait associated types (`Self::Item`) and predicates
                // (`Self::step`) remain resolvable on it.
                let trait_ident = &item_trait.ident;
                let (_, ty_generics, _) = item_trait.generics.split_for_impl();
                def_wheres.push(syn::parse_quote!(#synth: #trait_ident #ty_generics));

                turbofish_args.push(quote!(Self));

                // Rewriting `Self` to the synthetic generic can yield predicates that
                // duplicate the synthetic generic's own `Model` bounds; drop the dups.
                let mut seen = std::collections::HashSet::new();
                def_wheres.retain(|pred| seen.insert(pred.to_token_stream().to_string()));
            }
        }
    }

    let model_ty_params = type_lowering.lower_params(&fn_params);
    let body = &body;

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

struct SelfValueRewriter {
    to: syn::Ident,
}

impl VisitMut for SelfValueRewriter {
    fn visit_pat_ident_mut(&mut self, pat: &mut syn::PatIdent) {
        if pat.ident == "self" {
            pat.ident = self.to.clone();
        }
        syn::visit_mut::visit_pat_ident_mut(self, pat);
    }

    fn visit_fn_arg_mut(&mut self, arg: &mut syn::FnArg) {
        match arg {
            syn::FnArg::Receiver(receiver) => {
                let to = &self.to;
                let ty = crate::receiver_type(receiver);
                *arg = syn::parse_quote!(#to: #ty);
            }
            syn::FnArg::Typed(_) => { /* handled by visit_pat_ident_mut */ }
        }

        syn::visit_mut::visit_fn_arg_mut(self, arg);
    }

    fn visit_expr_path_mut(&mut self, expr_path: &mut syn::ExprPath) {
        if expr_path.qself.is_some() {
            syn::visit_mut::visit_expr_path_mut(self, expr_path);
            return;
        }

        if expr_path.path.leading_colon.is_some() || expr_path.path.segments.len() != 1 {
            syn::visit_mut::visit_expr_path_mut(self, expr_path);
            return;
        }

        if expr_path.path.segments[0].ident == "self" {
            expr_path.path.segments[0].ident = self.to.clone();
            return;
        }

        syn::visit_mut::visit_expr_path_mut(self, expr_path);
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if !is_formula_macro(&mac.path) {
            syn::visit_mut::visit_macro_mut(self, mac);
            return;
        }

        let expanded = crate::formula::expand(mac.tokens.clone());
        let Ok(mut expr) = syn::parse2::<syn::Expr>(expanded) else {
            return;
        };
        self.visit_expr_mut(&mut expr);
        mac.tokens = expr.into_token_stream();
    }
}

struct SelfTypeRewriter {
    to: syn::Type,
}

impl VisitMut for SelfTypeRewriter {
    fn visit_type_mut(&mut self, ty: &mut syn::Type) {
        syn::visit_mut::visit_type_mut(self, ty);

        let syn::Type::Path(type_path) = ty else {
            return;
        };

        if type_path.qself.is_some() || type_path.path.leading_colon.is_some() {
            return;
        }

        let mut segments = type_path.path.segments.iter();

        if segments.next().is_none_or(|first| first.ident != "Self") {
            return;
        }

        let tail: syn::punctuated::Punctuated<_, syn::Token![::]> = segments.cloned().collect();

        if tail.is_empty() {
            *ty = self.to.clone();
        } else {
            let to = &self.to;
            *ty = syn::parse_quote!(<#to>::#tail)
        };
    }

    fn visit_expr_path_mut(&mut self, expr_path: &mut syn::ExprPath) {
        syn::visit_mut::visit_expr_path_mut(self, expr_path);

        if expr_path.qself.is_some() || expr_path.path.leading_colon.is_some() {
            return;
        }

        let mut segments = expr_path.path.segments.iter();

        if segments.next().is_none_or(|first| first.ident != "Self") {
            return;
        }

        let tail: syn::punctuated::Punctuated<_, syn::Token![::]> = segments.cloned().collect();

        if tail.is_empty() {
            return;
        }

        let to = &self.to;
        *expr_path = syn::parse_quote!(<#to>::#tail);
    }

    fn visit_macro_mut(&mut self, mac: &mut syn::Macro) {
        if !is_formula_macro(&mac.path) {
            syn::visit_mut::visit_macro_mut(self, mac);
            return;
        }

        let expanded = crate::formula::expand(mac.tokens.clone());
        let Ok(mut expr) = syn::parse2::<syn::Expr>(expanded) else {
            return;
        };
        self.visit_expr_mut(&mut expr);
        mac.tokens = expr.into_token_stream();
    }
}

fn is_formula_macro(path: &syn::Path) -> bool {
    // TODO: identify the macro precisely
    path.segments
        .last()
        .is_some_and(|seg| seg.ident == "formula")
}
