//! Expansion of `#[thrust_macros::invariant_context]`.
//!
//! Threads the surrounding generic context (and, in methods, `Self`) into
//! every `thrust_macros::invariant!(...)` call inside the annotated item. Each
//! such call is replaced in-place by an expanded `#[thrust::formula_fn]` plus
//! a marker call, with the threaded generics declared on the formula function
//! and instantiated via turbofish. In methods, `Self` is re-declared as a
//! synthetic type parameter and instantiated with the real `Self` the same
//! way, so an invariant may refer to generic- and `Self`-typed variables that
//! the standalone `invariant!` macro cannot see.
//!
//! The host function's where clause gains `T: Model` and
//! `<T as Model>::Ty: PartialEq` predicates for every in-scope type parameter
//! (and for `Self` when used), as the generated marker call instantiates a
//! `Model`-bounded function.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree};
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, visit_mut::VisitMut, FnArg, GenericParam, Generics, WherePredicate};

use crate::{fn_params_with_model_ty, FnOuterItem};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

pub(super) fn expand(item: TokenStream) -> TokenStream {
    let mut item = parse_macro_input!(item as syn::Item);

    match &mut item {
        syn::Item::Fn(item_fn) => {
            let generics = item_fn.sig.generics.clone();
            let mut rewriter = InvariantRewriter::new(&generics, None);
            rewriter.visit_block_mut(&mut item_fn.block);
            if rewriter.found {
                inject_model_bounds(&mut item_fn.sig.generics, None, rewriter.self_used);
            }
        }
        syn::Item::Impl(item_impl) => {
            let outer = FnOuterItem::ItemImpl(item_impl.clone()).into_header_only();
            for impl_item in &mut item_impl.items {
                let syn::ImplItem::Fn(method) = impl_item else {
                    continue;
                };
                let generics = method.sig.generics.clone();
                let mut rewriter = InvariantRewriter::new(&generics, Some(&outer));
                rewriter.visit_block_mut(&mut method.block);
                if rewriter.found {
                    inject_model_bounds(&mut method.sig.generics, Some(&outer), rewriter.self_used);
                }
            }
        }
        syn::Item::Trait(item_trait) => {
            let outer = FnOuterItem::ItemTrait(item_trait.clone()).into_header_only();
            for trait_item in &mut item_trait.items {
                let syn::TraitItem::Fn(method) = trait_item else {
                    continue;
                };
                let Some(block) = &mut method.default else {
                    continue;
                };
                let generics = method.sig.generics.clone();
                let mut rewriter = InvariantRewriter::new(&generics, Some(&outer));
                rewriter.visit_block_mut(block);
                if rewriter.found {
                    inject_model_bounds(&mut method.sig.generics, Some(&outer), rewriter.self_used);
                }
            }
        }
        _ => {
            return syn::Error::new_spanned(
                &item,
                "#[thrust_macros::invariant_context] expects a function, impl block, or trait \
                 definition",
            )
            .to_compile_error()
            .into();
        }
    }

    item.into_token_stream().into()
}

struct InvariantRewriter {
    /// In-scope generic params (the function's own, plus the outer impl/trait's
    /// own for a method).
    params: Vec<GenericParam>,
    /// Combined where-predicates from the function and (for a method) the
    /// outer impl/trait. `Model`/`PartialEq` bounds for `params` are added
    /// when constructing the formula function so each turbofish argument
    /// satisfies them.
    wheres: Vec<WherePredicate>,
    is_method: bool,
    found: bool,
    self_used: bool,
}

impl InvariantRewriter {
    fn new(fn_generics: &Generics, outer: Option<&FnOuterItem>) -> Self {
        let mut params: Vec<GenericParam> = fn_generics.params.iter().cloned().collect();
        let mut wheres: Vec<WherePredicate> = fn_generics
            .where_clause
            .as_ref()
            .map(|wc| wc.predicates.iter().cloned().collect())
            .unwrap_or_default();
        if let Some(outer) = outer {
            params.extend(outer.generics().params.iter().cloned());
            if let Some(wc) = &outer.generics().where_clause {
                wheres.extend(wc.predicates.iter().cloned());
            }
        }
        Self {
            params,
            wheres,
            is_method: outer.is_some(),
            found: false,
            self_used: false,
        }
    }

    /// Builds the expansion for a single `invariant!` macro call.
    fn expand_invariant(&mut self, mac: &syn::Macro) -> syn::Expr {
        let closure: syn::ExprClosure = match syn::parse2(mac.tokens.clone()) {
            Ok(c) => c,
            Err(e) => return syn::Expr::Verbatim(e.to_compile_error()),
        };

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
        let mut def_wheres: Vec<TokenStream2> =
            self.wheres.iter().map(|w| w.to_token_stream()).collect();
        let mut turbofish_args: Vec<TokenStream2> = Vec::new();

        // `Self` in a method context: rewrite to a synthetic generic, then
        // pass the real `Self` via turbofish (legal in expression position).
        let uses_self = self.is_method && tokens_contain_self(&closure.to_token_stream());
        if uses_self {
            self.self_used = true;
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

        let model_ty_params = fn_params_with_model_ty(&fn_params);
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
}

impl VisitMut for InvariantRewriter {
    fn visit_stmt_mut(&mut self, stmt: &mut syn::Stmt) {
        syn::visit_mut::visit_stmt_mut(self, stmt);
        if let syn::Stmt::Macro(stmt_macro) = stmt {
            if is_invariant_macro(&stmt_macro.mac.path) {
                self.found = true;
                let expanded = self.expand_invariant(&stmt_macro.mac);
                *stmt = syn::Stmt::Expr(expanded, stmt_macro.semi_token);
            }
        }
    }

    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);
        if let syn::Expr::Macro(expr_macro) = expr {
            if is_invariant_macro(&expr_macro.mac.path) {
                self.found = true;
                *expr = self.expand_invariant(&expr_macro.mac);
            }
        }
    }
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

/// Adds `T: Model` and `<T as Model>::Ty: PartialEq` bounds for every type
/// parameter in scope to a function's where clause. Each marker call generated
/// by the rewriter instantiates a `Model`-bounded formula function, so the
/// host function must itself satisfy those bounds. When an invariant names
/// `Self`, the rewriter instantiates the formula function with `Self`, so the
/// same bounds are added for `Self` (`with_self`).
fn inject_model_bounds(generics: &mut Generics, outer: Option<&FnOuterItem>, with_self: bool) {
    let mut tys: Vec<TokenStream2> = generics
        .params
        .iter()
        .filter_map(|p| match p {
            GenericParam::Type(tp) => Some(tp.ident.to_token_stream()),
            _ => None,
        })
        .collect();
    if let Some(outer) = outer {
        for param in &outer.generics().params {
            if let GenericParam::Type(tp) = param {
                tys.push(tp.ident.to_token_stream());
            }
        }
    }
    if with_self {
        tys.push(quote!(Self));
    }
    if tys.is_empty() {
        return;
    }
    let where_clause = generics.make_where_clause();
    for ty in tys {
        where_clause
            .predicates
            .push(syn::parse_quote!(#ty: thrust_models::Model));
        where_clause
            .predicates
            .push(syn::parse_quote!(<#ty as thrust_models::Model>::Ty: PartialEq));
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
