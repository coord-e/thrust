//! Lifting a formula written inside a function body into a standalone
//! `#[thrust::formula_fn]` item that a marker call refers to.
//!
//! The item is a free function, so it inherits neither the enclosing function's generics
//! nor `Self`: a formula naming a generic- or `Self`-typed variable only type-checks once
//! those are re-declared on it and instantiated where it is referred to.
//! [`EnclosingContext`] carries what to re-declare, threaded in by
//! `#[thrust_macros::context]`; without it a formula only sees concrete types.

use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    visit_mut::VisitMut,
    FnArg, GenericParam, Signature, WherePredicate,
};

use crate::{fn_outer_item::FnOuterItem, FormulaFnTypeLowering};

/// The context a formula is written in: the host function's signature and, for a method,
/// its `impl`/`trait` header.
pub struct EnclosingContext {
    sig: Signature,
    outer: Option<FnOuterItem>,
}

impl Parse for EnclosingContext {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let attrs = input.call(syn::Attribute::parse_outer)?;
        let outer = crate::extract_outer_context(&attrs)?;
        let sig: Signature = input.parse()?;
        input.parse::<syn::Token![;]>()?;
        Ok(Self { sig, outer })
    }
}

impl EnclosingContext {
    /// The generic params in scope: the host signature's own, plus the outer
    /// `impl`/`trait`'s for a method.
    fn generic_params(&self) -> impl Iterator<Item = &GenericParam> {
        self.sig
            .generics
            .params
            .iter()
            .chain(self.outer.iter().flat_map(|o| o.generics().params.iter()))
    }

    /// The where-predicates in scope, from the host signature and (for a method) the
    /// outer `impl`/`trait`.
    fn where_predicates(&self) -> impl Iterator<Item = &WherePredicate> {
        fn preds(g: &syn::Generics) -> impl Iterator<Item = &WherePredicate> {
            g.where_clause.iter().flat_map(|wc| wc.predicates.iter())
        }
        preds(&self.sig.generics).chain(self.outer.iter().flat_map(|o| preds(o.generics())))
    }

    fn type_lowering(&self) -> FormulaFnTypeLowering<'_> {
        match &self.outer {
            Some(outer) => FormulaFnTypeLowering::with_outer_context(&self.sig, outer),
            None => FormulaFnTypeLowering::new(&self.sig),
        }
    }
}

/// A spec macro's closure together with the context it was written in, the form
/// `#[thrust_macros::context]` rewrites the macro's tokens into.
pub struct ClosureWithContext {
    pub context: EnclosingContext,
    pub closure: syn::ExprClosure,
}

impl Parse for ClosureWithContext {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let context = input.parse()?;
        let closure = input.parse()?;
        Ok(Self { context, closure })
    }
}

/// A formula lifted into a `#[thrust::formula_fn]` item, with the expression naming that
/// item — generic arguments included — for the marker call to take.
pub struct LiftedFormulaFn {
    pub item: syn::ItemFn,
    pub reference: syn::Expr,
}

/// Lifts `body`, a formula over `params`, into a `#[thrust::formula_fn]` called `name`.
///
/// The parameters are lowered to their model types. The receiver `self` is renamed to
/// `__thrust_self`, which the analyzer binds back to the receiver value. Under a
/// `context`, the generics in scope there are re-declared on the item and instantiated at
/// the reference; in a method, `Self` becomes the concrete self type of the `impl`, or a
/// synthetic type parameter instantiated with the real `Self` in a trait.
pub fn lift(
    name: &syn::Ident,
    params: &[FnArg],
    body: &syn::Expr,
    context: Option<&EnclosingContext>,
) -> syn::Result<LiftedFormulaFn> {
    let mut params = params.to_vec();
    let mut body = body.clone();

    let mut def_params: Vec<TokenStream2> = Vec::new();
    let mut turbofish_args: Vec<TokenStream2> = Vec::new();
    for param in context
        .into_iter()
        .flat_map(EnclosingContext::generic_params)
    {
        def_params.push(param.to_token_stream());
        match param {
            GenericParam::Type(tp) => turbofish_args.push(tp.ident.to_token_stream()),
            GenericParam::Const(cp) => turbofish_args.push(cp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => {}
        }
    }

    let mut def_wheres: Vec<WherePredicate> = context
        .into_iter()
        .flat_map(EnclosingContext::where_predicates)
        .cloned()
        .collect();

    let dummy_sig = syn::parse_quote!(fn f());
    let type_lowering = match context {
        Some(context) => context.type_lowering(),
        None => FormulaFnTypeLowering::new(&dummy_sig),
    };

    def_wheres.extend(type_lowering.model_where_predicates());

    // A formula may refer to the receiver value `self`; the lifted formula function is free, so
    // rewrite `self` to a `__thrust_self` parameter. The analyzer binds it back to the receiver.
    let mut rewriter = SelfValueRewriter {
        to: format_ident!("__thrust_self"),
    };
    for param in &mut params {
        rewriter.visit_fn_arg_mut(param);
    }
    rewriter.visit_expr_mut(&mut body);

    let self_used = params
        .iter()
        .any(|param| crate::tokens_contain_ident(&param.to_token_stream(), "Self"))
        || crate::tokens_contain_ident(&body.to_token_stream(), "Self")
        || def_wheres
            .iter()
            .any(|pred| crate::tokens_contain_ident(&pred.to_token_stream(), "Self"));
    if self_used {
        let Some(outer) = context.and_then(|context| context.outer.as_ref()) else {
            return Err(syn::Error::new_spanned(
                body,
                "formula cannot refer to `Self` without an enclosing impl/trait context",
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
                for param in &mut params {
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
                for param in &mut params {
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

    let model_ty_params = type_lowering.lower_params(&params);

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

    Ok(LiftedFormulaFn {
        item: syn::parse_quote!(
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #name #def_generics(#model_ty_params) -> bool #where_clause {
                #body
            }
        ),
        reference: syn::parse_quote!(#name #turbofish),
    })
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
