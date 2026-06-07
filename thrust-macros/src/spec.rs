//! Expansion of `#[thrust_macros::requires]`, `#[thrust_macros::ensures]`,
//! `#[thrust_macros::predicate]`, and the internal `_requires_ensures` glue.
//!
//! `requires`/`ensures` accumulate their predicates into a single
//! `_requires_ensures` attribute, which expands into `#[thrust::formula_fn]`
//! companions (over `Model::Ty` parameters) plus an extern-spec wrapper that
//! references them.

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, punctuated::Punctuated, FnArg, GenericParam, Generics, WherePredicate,
};

use crate::{fn_outer_item::FnOuterItem, FormulaFnTypeLowering};

pub fn expand_predicate(item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let name = &func.sig().ident;
    let def_generics = generic_params_tokens(&func.sig().generics);
    let type_lowering = if let Some(outer_context) = &outer_context {
        FormulaFnTypeLowering::with_outer_context(func.sig(), outer_context)
    } else {
        FormulaFnTypeLowering::new(func.sig())
    };
    let model_ty_params = type_lowering.lower_params(&func.sig().inputs);
    let model_ret = type_lowering.lower_return_type(&func.sig().output);

    let model_preds = type_lowering.model_where_predicates();
    let extended_where = extended_where_clause(&func, &model_preds);

    let sig = quote! {
        #[allow(dead_code)]
        #[thrust::predicate]
        fn #name #def_generics(#model_ty_params) -> #model_ret #extended_where
    };
    if let Some(block) = func.block() {
        quote! { #sig #block }.into()
    } else {
        quote! { #sig; }.into()
    }
}

pub fn expand_requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs_mut().push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures((#req_expr) && (#expr), #ens_expr)]
    ));

    func.into_token_stream().into()
}

pub fn expand_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs_mut().push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures(#req_expr, (#ens_expr) && (#expr))]
    ));

    func.into_token_stream().into()
}

pub fn expand_requires_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    use syn::parse::Parser as _;
    let parser = Punctuated::<syn::Expr, syn::Token![,]>::parse_separated_nonempty;
    let mut exprs = match parser.parse(attr.clone()) {
        Ok(exprs) => exprs,
        Err(e) => return e.to_compile_error().into(),
    };
    if exprs.len() != 2 {
        return syn::Error::new_spanned(
            TokenStream2::from(attr),
            "expected exactly two comma-separated expressions in _requires_ensures attribute",
        )
        .to_compile_error()
        .into();
    }

    let ens_expr = exprs.pop().unwrap().into_value();
    let req_expr = exprs.pop().unwrap().into_value();

    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let mut tokens = ExpandedTokens::new(func, req_expr, ens_expr);
    if let Some(ctx) = outer_context {
        tokens = tokens.with_outer_context(ctx);
    }
    tokens.into_token_stream().into()
}

#[allow(clippy::enum_variant_names)]
#[derive(Debug, Clone)]
enum FnItemWithSignature {
    ItemFn(syn::ItemFn),
    ImplItemFn(syn::ImplItemFn),
    TraitItemFn(syn::TraitItemFn),
}

impl syn::parse::Parse for FnItemWithSignature {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative as _;

        let fork = input.fork();
        if let Ok(item_fn) = fork.parse::<syn::ItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::ItemFn(item_fn));
        }

        let fork = input.fork();
        if let Ok(impl_item_fn) = fork.parse::<syn::ImplItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::ImplItemFn(impl_item_fn));
        }

        let fork = input.fork();
        if let Ok(trait_item_fn) = fork.parse::<syn::TraitItemFn>() {
            input.advance_to(&fork);
            return Ok(Self::TraitItemFn(trait_item_fn));
        }

        Err(input.error("expected a free function, an impl method, or a trait method"))
    }
}

impl quote::ToTokens for FnItemWithSignature {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => item_fn.to_tokens(tokens),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => impl_item_fn.to_tokens(tokens),
            FnItemWithSignature::TraitItemFn(trait_item_fn) => trait_item_fn.to_tokens(tokens),
        }
    }
}

impl FnItemWithSignature {
    fn block(&self) -> Option<&syn::Block> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => Some(&item_fn.block),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => Some(&impl_item_fn.block),
            FnItemWithSignature::TraitItemFn(_) => None,
        }
    }

    fn block_mut(&mut self) -> Option<&mut syn::Block> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => Some(&mut item_fn.block),
            FnItemWithSignature::ImplItemFn(impl_item_fn) => Some(&mut impl_item_fn.block),
            FnItemWithSignature::TraitItemFn(_) => None,
        }
    }

    fn attrs(&self) -> &[syn::Attribute] {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &item_fn.attrs,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &impl_item_fn.attrs,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &trait_item_fn.attrs,
        }
    }

    fn attrs_mut(&mut self) -> &mut Vec<syn::Attribute> {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &mut item_fn.attrs,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &mut impl_item_fn.attrs,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &mut trait_item_fn.attrs,
        }
    }

    fn sig(&self) -> &syn::Signature {
        match self {
            FnItemWithSignature::ItemFn(item_fn) => &item_fn.sig,
            FnItemWithSignature::ImplItemFn(impl_item_fn) => &impl_item_fn.sig,
            FnItemWithSignature::TraitItemFn(trait_item_fn) => &trait_item_fn.sig,
        }
    }
}

fn extract_requires_ensures(func: &mut FnItemWithSignature) -> syn::Result<(syn::Expr, syn::Expr)> {
    let mut result = None;

    let requires_ensures_path: syn::Path = syn::parse_quote!(::thrust_macros::_requires_ensures);

    for attr in func.attrs() {
        if attr.path() == &requires_ensures_path {
            if result.is_some() {
                return Err(syn::Error::new_spanned(
                    attr,
                    "multiple _requires_ensures attributes found; expected at most one",
                ));
            }

            let parser = Punctuated::<syn::Expr, syn::Token![,]>::parse_separated_nonempty;
            let mut exprs = attr.parse_args_with(parser)?;
            if exprs.len() != 2 {
                return Err(syn::Error::new_spanned(
                    attr,
                    "expected exactly two comma-separated expressions in _requires_ensures attribute",
                ));
            }
            let ens_expr = exprs.pop().unwrap().into_value();
            let req_expr = exprs.pop().unwrap().into_value();
            result = Some((req_expr, ens_expr));
        }
    }

    func.attrs_mut()
        .retain(|attr| attr.path() != &requires_ensures_path);

    if let Some((req_expr, ens_expr)) = result {
        Ok((req_expr, ens_expr))
    } else {
        Ok((syn::parse_quote!(true), syn::parse_quote!(true)))
    }
}

fn extract_outer_context(func: &FnItemWithSignature) -> syn::Result<Option<FnOuterItem>> {
    let outer_context = crate::extract_outer_context(func.attrs())?;
    if mentions_self(func.sig()) && outer_context.is_none() {
        return Err(syn::Error::new_spanned(
            func.sig().ident.clone(),
            "Wrap the surrounding impl block or trait definition with #[thrust_macros::context] to annotate methods",
        ));
    }
    Ok(outer_context)
}

struct ExpandedTokens {
    func: FnItemWithSignature,

    requires_name: syn::Ident,
    ensures_name: syn::Ident,
    req_expr: syn::Expr,
    ens_expr: syn::Expr,

    def_generics: TokenStream2,
    turbofish: TokenStream2,

    outer_context: Option<FnOuterItem>,
}

impl quote::ToTokens for ExpandedTokens {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        if self.is_extern_spec_fn() {
            self.expand_extern_spec_fn().to_tokens(tokens);
        } else {
            self.expand().to_tokens(tokens);
        }
    }
}

impl ExpandedTokens {
    fn new(func: FnItemWithSignature, mut req_expr: syn::Expr, mut ens_expr: syn::Expr) -> Self {
        let name = &func.sig().ident;
        let requires_name = format_ident!("_thrust_requires_{}", name);
        let ensures_name = format_ident!("_thrust_ensures_{}", name);

        let generics = &func.sig().generics;
        let def_generics = generic_params_tokens(generics);
        let turbofish = generic_turbofish(generics);

        if func.sig().receiver().is_some() {
            rewrite_self_in_expr(&mut req_expr);
            rewrite_self_in_expr(&mut ens_expr);
        }

        Self {
            func,
            req_expr,
            ens_expr,
            requires_name,
            ensures_name,
            def_generics,
            turbofish,
            outer_context: None,
        }
    }

    fn with_outer_context(mut self, outer_item: FnOuterItem) -> Self {
        self.outer_context = Some(outer_item);
        self
    }

    fn type_lowering(&self) -> FormulaFnTypeLowering<'_> {
        if let Some(outer_context) = &self.outer_context {
            FormulaFnTypeLowering::with_outer_context(self.func.sig(), outer_context)
        } else {
            FormulaFnTypeLowering::new(self.func.sig())
        }
    }

    fn extended_where_clause(&self) -> TokenStream2 {
        let model_preds = self.type_lowering().model_where_predicates();
        extended_where_clause(&self.func, &model_preds)
    }

    fn is_extern_spec_fn(&self) -> bool {
        let extern_spec_fn_path: syn::Path = syn::parse_quote!(thrust::extern_spec_fn);
        self.func
            .attrs()
            .iter()
            .any(|a| a.path() == &extern_spec_fn_path)
    }

    fn requires_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let def_generics = &self.def_generics;
        let model_ty_params = self.type_lowering().lower_params(&self.func.sig().inputs);
        let extended_where = self.extended_where_clause();
        let req_expr = &self.req_expr;

        quote! {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #requires_name #def_generics(#model_ty_params) -> bool #extended_where {
                #req_expr
            }
        }
    }

    fn ensures_fn(&self) -> TokenStream2 {
        let ensures_name = &self.ensures_name;
        let def_generics = &self.def_generics;
        let model_ty_params = &self.type_lowering().lower_params(&self.func.sig().inputs);
        let extended_where = self.extended_where_clause();
        let ret_model_ty = &self
            .type_lowering()
            .lower_return_type(&self.func.sig().output);
        let ens_expr = &self.ens_expr;

        quote! {
            #[allow(unused_variables)]
            #[allow(non_snake_case)]
            #[thrust::formula_fn]
            fn #ensures_name #def_generics(result: #ret_model_ty, #model_ty_params) -> bool #extended_where {
                #ens_expr
            }
        }
    }

    fn path_prefix(&self) -> Option<TokenStream2> {
        self.outer_context.as_ref()?;
        Some(quote!(Self::))
    }

    fn expand(&self) -> TokenStream2 {
        let mut func = self.func.clone();
        let trusted_path: syn::Path = syn::parse_quote!(thrust::trusted);
        for attr in func.attrs_mut() {
            if attr.path() == &trusted_path {
                *attr = syn::parse_quote!(#[thrust::ignored]);
            }
        }

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        let extern_spec_name = format_ident!("_thrust_extern_spec_{}", self.func.sig().ident);
        let def_generics = &self.def_generics;
        let orig_output = &self.func.sig().output;
        let extended_where = self.extended_where_clause();

        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;
        let path_prefix = self.path_prefix();

        let name = &self.func.sig().ident;
        let (extern_spec_inputs, call_args) = rewrite_inputs_for_call(&self.func.sig().inputs);

        quote! {
            #func

            #requires_fn
            #ensures_fn

            #[thrust::extern_spec_fn]
            #[allow(path_statements)]
            fn #extern_spec_name #def_generics(#extern_spec_inputs) #orig_output #extended_where {
                #[thrust::requires_path]
                #path_prefix #requires_name #turbofish;

                #[thrust::ensures_path]
                #path_prefix #ensures_name #turbofish;

                #path_prefix #name #turbofish(#call_args)
            }
        }
    }

    fn expand_extern_spec_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;
        let path_prefix = self.path_prefix();

        let mut func = self.func.clone();
        let func_tokens = if let Some(block) = func.block_mut() {
            let orig_stmts = block.stmts.drain(..).collect::<Vec<_>>();
            *block = syn::parse_quote!({
                #[thrust::requires_path]
                #path_prefix #requires_name #turbofish;

                #[thrust::ensures_path]
                #path_prefix #ensures_name #turbofish;

                #(#orig_stmts)*
            });
            quote! {
                #[allow(path_statements)]
                #func
            }
        } else {
            let error = syn::Error::new_spanned(
                func.sig().ident.clone(),
                "extern_spec_fn must have a function body",
            )
            .into_compile_error();
            quote! {
                #error
                #func
            }
        };

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        quote! {
            #requires_fn
            #ensures_fn

            #func_tokens
        }
    }
}

fn mentions_self(sig: &syn::Signature) -> bool {
    struct Visitor {
        mentions_self: bool,
    }

    impl syn::visit::Visit<'_> for Visitor {
        fn visit_ident(&mut self, i: &syn::Ident) {
            if i == "self" || i == "Self" {
                self.mentions_self = true;
            }
        }
    }

    let mut visitor = Visitor {
        mentions_self: false,
    };
    use syn::visit::Visit as _;
    visitor.visit_signature(sig);
    visitor.mentions_self
}

fn rewrite_self_in_expr(expr: &mut syn::Expr) {
    struct Visitor;

    impl syn::visit_mut::VisitMut for Visitor {
        fn visit_ident_mut(&mut self, ident: &mut syn::Ident) {
            if ident == "self" {
                *ident = format_ident!("self_");
            }
        }
    }

    use syn::visit_mut::VisitMut as _;
    Visitor.visit_expr_mut(expr);
}

/// Returns `<T: Bound, U, 'a>` — the generic param list for function definitions,
/// without a where clause.
fn generic_params_tokens(generics: &Generics) -> TokenStream2 {
    if generics.params.is_empty() {
        return quote!();
    }
    let params = &generics.params;
    quote!(<#params>)
}

/// Returns `::<T, U>` for turbofish use, or nothing if no generic params.
fn generic_turbofish(generics: &Generics) -> TokenStream2 {
    let args: Vec<TokenStream2> = generics
        .params
        .iter()
        .flat_map(|p| match p {
            GenericParam::Type(tp) => Some(tp.ident.to_token_stream()),
            GenericParam::Lifetime(_) => None,
            GenericParam::Const(cp) => Some(cp.ident.to_token_stream()),
        })
        .collect();
    if args.is_empty() {
        return quote!();
    }
    quote!(::<#(#args),*>)
}

/// For the extern_spec wrapper: replaces every typed parameter with a fresh `_arg_N` ident,
/// returning `(rewritten_inputs_tokens, call_args_tokens)`.
fn rewrite_inputs_for_call(
    inputs: &syn::punctuated::Punctuated<FnArg, syn::token::Comma>,
) -> (TokenStream2, TokenStream2) {
    let mut rewritten: Vec<TokenStream2> = Vec::new();
    let mut call_args: Vec<TokenStream2> = Vec::new();

    for (i, arg) in inputs.iter().enumerate() {
        match arg {
            FnArg::Typed(pt) => {
                let fresh = format_ident!("_arg_{}", i);
                let ty = &pt.ty;
                rewritten.push(quote!(#fresh: #ty));
                call_args.push(fresh.to_token_stream());
            }
            FnArg::Receiver(_) => {
                rewritten.push(arg.to_token_stream());
                call_args.push(quote!(self));
            }
        }
    }

    (quote!(#(#rewritten),*), quote!(#(#call_args),*))
}

/// Builds `where <original predicates>, <model predicates>`.
/// Returns an empty token stream when both sets are empty.
fn extended_where_clause(
    func: &FnItemWithSignature,
    model_preds: &Vec<syn::WherePredicate>,
) -> TokenStream2 {
    let existing: Vec<&WherePredicate> = func
        .sig()
        .generics
        .where_clause
        .as_ref()
        .map(|wc| wc.predicates.iter().collect())
        .unwrap_or_default();

    if existing.is_empty() && model_preds.is_empty() {
        return quote!();
    }

    quote! { where #(#existing,)* #(#model_preds),* }
}
