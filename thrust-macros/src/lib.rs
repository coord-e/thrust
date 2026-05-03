use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use std::collections::HashSet;
use syn::{
    punctuated::Punctuated, FnArg, GenericParam, Generics, ItemFn,
    LifetimeParam, ReturnType, TraitItemFn, Type, TypeParamBound, WherePredicate,
};
use syn::visit_mut::VisitMut;

#[proc_macro_attribute]
pub fn predicate(_attr: TokenStream, item: TokenStream) -> TokenStream {
    if let Ok(mut func) = syn::parse::<ItemFn>(item.clone()) {
        rewrite_predicate_sig_and_attrs(&mut func.sig, &mut func.attrs);
        return func.into_token_stream().into();
    }
    if let Ok(mut func) = syn::parse::<TraitItemFn>(item.clone()) {
        rewrite_predicate_sig_and_attrs(&mut func.sig, &mut func.attrs);
        return func.into_token_stream().into();
    }
    syn::Error::new(proc_macro2::Span::call_site(), "expected a function or trait method")
        .to_compile_error()
        .into()
}

fn rewrite_predicate_sig_and_attrs(sig: &mut syn::Signature, attrs: &mut Vec<syn::Attribute>) {
    let predicate_path: syn::Path = syn::parse_quote!(::thrust_macros::predicate);
    attrs.retain(|a| a.path() != &predicate_path);
    attrs.push(syn::parse_quote!(#[thrust::predicate]));

    elaborate_receiver_lifetime(&mut sig.inputs, &mut sig.generics);
    elaborate_typed_param_lifetimes(&mut sig.inputs, &mut sig.generics);

    let fn_bounds = fn_has_fn_bounds(&sig.generics);
    let model_preds = model_predicates_from_params(&sig.inputs, &fn_bounds);

    let new_inputs: Punctuated<FnArg, syn::token::Comma> = sig
        .inputs
        .iter()
        .map(|arg| -> FnArg {
            match arg {
                FnArg::Receiver(recv) => {
                    let model_ty = receiver_model_ty(recv);
                    syn::parse_quote!(self_: #model_ty)
                }
                FnArg::Typed(pt) => {
                    let pat = &pt.pat;
                    let ty = &pt.ty;
                    let model_ty: Type = syn::parse_quote!(<#ty as thrust_models::Model>::Ty);
                    syn::parse_quote!(#pat: #model_ty)
                }
            }
        })
        .collect();
    sig.inputs = new_inputs;

    let wc = sig.generics.where_clause.get_or_insert_with(|| syn::WhereClause {
        where_token: Default::default(),
        predicates: Punctuated::new(),
    });
    for pred in model_preds {
        wc.predicates.push(pred);
    }
}

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);

    if let Ok(mut func) = syn::parse::<ItemFn>(item.clone()) {
        let (req_expr, ens_expr) = match extract_requires_ensures(&mut func.attrs) {
            Ok(r) => r,
            Err(e) => return e.to_compile_error().into(),
        };
        func.attrs.push(syn::parse_quote!(
            #[::thrust_macros::_requires_ensures((#req_expr) && (#expr), #ens_expr)]
        ));
        return func.into_token_stream().into();
    }

    if let Ok(mut func) = syn::parse::<TraitItemFn>(item.clone()) {
        let (req_expr, ens_expr) = match extract_requires_ensures(&mut func.attrs) {
            Ok(r) => r,
            Err(e) => return e.to_compile_error().into(),
        };
        func.attrs.push(syn::parse_quote!(
            #[::thrust_macros::_requires_ensures((#req_expr) && (#expr), #ens_expr)]
        ));
        return func.into_token_stream().into();
    }

    syn::Error::new(proc_macro2::Span::call_site(), "expected a function or trait method")
        .to_compile_error()
        .into()
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);

    if let Ok(mut func) = syn::parse::<ItemFn>(item.clone()) {
        let (req_expr, ens_expr) = match extract_requires_ensures(&mut func.attrs) {
            Ok(r) => r,
            Err(e) => return e.to_compile_error().into(),
        };
        func.attrs.push(syn::parse_quote!(
            #[::thrust_macros::_requires_ensures(#req_expr, (#ens_expr) && (#expr))]
        ));
        return func.into_token_stream().into();
    }

    if let Ok(mut func) = syn::parse::<TraitItemFn>(item.clone()) {
        let (req_expr, ens_expr) = match extract_requires_ensures(&mut func.attrs) {
            Ok(r) => r,
            Err(e) => return e.to_compile_error().into(),
        };
        func.attrs.push(syn::parse_quote!(
            #[::thrust_macros::_requires_ensures(#req_expr, (#ens_expr) && (#expr))]
        ));
        return func.into_token_stream().into();
    }

    syn::Error::new(proc_macro2::Span::call_site(), "expected a function or trait method")
        .to_compile_error()
        .into()
}

fn extract_requires_ensures(attrs: &mut Vec<syn::Attribute>) -> syn::Result<(syn::Expr, syn::Expr)> {
    let mut result = None;

    let requires_ensures_path: syn::Path = syn::parse_quote!(::thrust_macros::_requires_ensures);

    for attr in attrs.iter() {
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

    attrs.retain(|attr| attr.path() != &requires_ensures_path);

    if let Some((req_expr, ens_expr)) = result {
        Ok((req_expr, ens_expr))
    } else {
        Ok((syn::parse_quote!(true), syn::parse_quote!(true)))
    }
}

#[proc_macro_attribute]
pub fn _requires_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
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

    if let Ok(func) = syn::parse::<ItemFn>(item.clone()) {
        return ExpandedTokens::new(func, req_expr, ens_expr)
            .into_token_stream()
            .into();
    }

    if let Ok(func) = syn::parse::<TraitItemFn>(item.clone()) {
        return ExpandedTokens::new_trait(func, req_expr, ens_expr)
            .into_token_stream()
            .into();
    }

    syn::Error::new(proc_macro2::Span::call_site(), "expected a function or trait method")
        .to_compile_error()
        .into()
}

enum FnItem {
    Free(ItemFn),
    Trait(TraitItemFn),
}

impl FnItem {
    fn sig(&self) -> &syn::Signature {
        match self {
            FnItem::Free(f) => &f.sig,
            FnItem::Trait(f) => &f.sig,
        }
    }
}

struct ExpandedTokens {
    item: FnItem,

    requires_name: syn::Ident,
    ensures_name: syn::Ident,
    req_expr: syn::Expr,
    ens_expr: syn::Expr,

    has_receiver: bool,

    def_generics: TokenStream2,
    turbofish: TokenStream2,
    extended_where: TokenStream2,

    model_ty_params: TokenStream2,
    ret_model_ty: Type,

    extern_spec_inputs: TokenStream2,
    call_args: TokenStream2,
}

impl quote::ToTokens for ExpandedTokens {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match &self.item {
            FnItem::Free(_) => {
                if self.is_extern_spec_fn() {
                    self.expand_extern_spec_fn().to_tokens(tokens);
                } else {
                    self.expand().to_tokens(tokens);
                }
            }
            FnItem::Trait(_) => self.expand_trait().to_tokens(tokens),
        }
    }
}

impl ExpandedTokens {
    fn from_sig(item: FnItem, req_expr: syn::Expr, ens_expr: syn::Expr) -> Self {
        let sig = item.sig();
        let name = &sig.ident;
        let requires_name = format_ident!("_thrust_requires_{}", name);
        let ensures_name = format_ident!("_thrust_ensures_{}", name);

        let has_receiver = matches!(sig.inputs.first(), Some(FnArg::Receiver(_)));

        // Rewrite `self` to `self_` in expressions when there's a receiver.
        let req_expr = if has_receiver { rewrite_self_in_expr(&req_expr) } else { req_expr };
        let ens_expr = if has_receiver { rewrite_self_in_expr(&ens_expr) } else { ens_expr };

        // Turbofish from original generics (before elaboration) — used at call sites.
        let turbofish = generic_turbofish(&sig.generics);

        // Clone sig and elaborate: insert fresh lifetimes into receiver and reference-typed params.
        let mut helper_inputs = sig.inputs.clone();
        let mut helper_generics = sig.generics.clone();
        elaborate_receiver_lifetime(&mut helper_inputs, &mut helper_generics);
        elaborate_typed_param_lifetimes(&mut helper_inputs, &mut helper_generics);

        let def_generics = generic_params_tokens(&helper_generics);

        let fn_bounds = fn_has_fn_bounds(&sig.generics);
        let model_preds = model_predicates_from_params(&helper_inputs, &fn_bounds);
        let extended_where = extended_where_clause(&helper_generics, &model_preds);

        let model_ty_params = fn_params_with_model_ty(&helper_inputs);
        let ret_model_ty: Type = match &sig.output {
            ReturnType::Default => syn::parse_quote!(<() as thrust_models::Model>::Ty),
            ReturnType::Type(_, ty) => syn::parse_quote!(<#ty as thrust_models::Model>::Ty),
        };

        let (extern_spec_inputs, call_args) = rewrite_inputs_for_call(&helper_inputs);

        Self {
            item,
            req_expr,
            ens_expr,
            requires_name,
            ensures_name,
            has_receiver,
            def_generics,
            turbofish,
            extended_where,
            model_ty_params,
            ret_model_ty,
            extern_spec_inputs,
            call_args,
        }
    }

    pub fn new(func: ItemFn, req_expr: syn::Expr, ens_expr: syn::Expr) -> Self {
        Self::from_sig(FnItem::Free(func), req_expr, ens_expr)
    }

    pub fn new_trait(func: TraitItemFn, req_expr: syn::Expr, ens_expr: syn::Expr) -> Self {
        Self::from_sig(FnItem::Trait(func), req_expr, ens_expr)
    }

    fn is_extern_spec_fn(&self) -> bool {
        let extern_spec_fn_path: syn::Path = syn::parse_quote!(thrust::extern_spec_fn);
        match &self.item {
            FnItem::Free(f) => f.attrs.iter().any(|a| a.path() == &extern_spec_fn_path),
            FnItem::Trait(_) => false,
        }
    }

    fn requires_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let def_generics = &self.def_generics;
        let model_ty_params = &self.model_ty_params;
        let extended_where = &self.extended_where;
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
        let model_ty_params = &self.model_ty_params;
        let extended_where = &self.extended_where;
        let ret_model_ty = &self.ret_model_ty;
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

    fn expand(&self) -> TokenStream2 {
        let FnItem::Free(func) = &self.item else { unreachable!() };
        let mut func = func.clone();
        let trusted_path: syn::Path = syn::parse_quote!(thrust::trusted);
        for attr in &mut func.attrs {
            if attr.path() == &trusted_path {
                *attr = syn::parse_quote!(#[thrust::ignored]);
            }
        }

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        let extern_spec_name = format_ident!("_thrust_extern_spec_{}", func.sig.ident);
        let def_generics = &self.def_generics;
        let orig_output = &func.sig.output;
        let extended_where = &self.extended_where;

        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;

        let name = &func.sig.ident;
        let extern_spec_inputs = &self.extern_spec_inputs;
        let call_args = &self.call_args;

        if self.has_receiver {
            quote! {
                #func

                #requires_fn
                #ensures_fn

                #[thrust::extern_spec_fn]
                #[allow(path_statements)]
                fn #extern_spec_name #def_generics(#extern_spec_inputs) #orig_output #extended_where {
                    #[thrust::requires_path]
                    Self::#requires_name;

                    #[thrust::ensures_path]
                    Self::#ensures_name;

                    Self::#name(#call_args)
                }
            }
        } else {
            quote! {
                #func

                #requires_fn
                #ensures_fn

                #[thrust::extern_spec_fn]
                #[allow(path_statements)]
                fn #extern_spec_name #def_generics(#extern_spec_inputs) #orig_output #extended_where {
                    #[thrust::requires_path]
                    #requires_name #turbofish;

                    #[thrust::ensures_path]
                    #ensures_name #turbofish;

                    #name #turbofish(#call_args)
                }
            }
        }
    }

    fn expand_extern_spec_fn(&self) -> TokenStream2 {
        let FnItem::Free(func) = &self.item else { unreachable!() };
        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;

        let mut func = func.clone();
        let orig_stmts = func.block.stmts.clone();
        func.block = syn::parse_quote!({
            #[thrust::requires_path]
            #requires_name #turbofish;

            #[thrust::ensures_path]
            #ensures_name #turbofish;

            #(#orig_stmts)*
        });

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        quote! {
            #requires_fn
            #ensures_fn

            #[allow(path_statements)]
            #func
        }
    }

    fn expand_trait(&self) -> TokenStream2 {
        let FnItem::Trait(func) = &self.item else { unreachable!() };
        let func = func.clone();

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        let fn_name = &func.sig.ident;
        let extern_spec_name = format_ident!("_thrust_extern_spec_{}", fn_name);
        let def_generics = &self.def_generics;
        let orig_output = &func.sig.output;
        let extended_where = &self.extended_where;

        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let extern_spec_inputs = &self.extern_spec_inputs;
        let call_args = &self.call_args;

        quote! {
            #requires_fn
            #ensures_fn

            #[thrust::extern_spec_fn]
            #[allow(path_statements)]
            fn #extern_spec_name #def_generics(#extern_spec_inputs) #orig_output #extended_where {
                #[thrust::requires_path]
                Self::#requires_name;

                #[thrust::ensures_path]
                Self::#ensures_name;

                Self::#fn_name(#call_args)
            }

            #func
        }
    }
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

/// Returns `::<T, U, 'a>` for turbofish use, or nothing if no generic params.
fn generic_turbofish(generics: &Generics) -> TokenStream2 {
    if generics.params.is_empty() {
        return quote!();
    }
    let args: Vec<TokenStream2> = generics
        .params
        .iter()
        .map(|p| match p {
            GenericParam::Type(tp) => tp.ident.to_token_stream(),
            GenericParam::Lifetime(lp) => lp.lifetime.to_token_stream(),
            GenericParam::Const(cp) => cp.ident.to_token_stream(),
        })
        .collect();
    quote!(::<#(#args),*>)
}

/// Returns a fresh lifetime not already declared in `generics.params`.
/// Tries 'a, 'b, 'c, ... in order.
fn fresh_lifetime(generics: &Generics) -> syn::Lifetime {
    let existing: HashSet<String> = generics
        .params
        .iter()
        .filter_map(|p| {
            if let GenericParam::Lifetime(lp) = p {
                Some(lp.lifetime.ident.to_string())
            } else {
                None
            }
        })
        .collect();
    for c in b'a'..=b'z' {
        let name = String::from(c as char);
        if !existing.contains(&name) {
            return syn::Lifetime::new(&format!("'{}", name), proc_macro2::Span::call_site());
        }
    }
    syn::Lifetime::new("'_thrust_lt", proc_macro2::Span::call_site())
}

/// Inserts a lifetime param after existing lifetimes but before type/const params.
fn insert_lifetime_param(generics: &mut Generics, lt: syn::Lifetime) {
    let pos = generics
        .params
        .iter()
        .take_while(|p| matches!(p, GenericParam::Lifetime(_)))
        .count();
    generics
        .params
        .insert(pos, GenericParam::Lifetime(LifetimeParam::new(lt)));
}

/// If receiver is `&self` or `&mut self` without a lifetime, inserts a fresh one.
fn elaborate_receiver_lifetime(
    inputs: &mut Punctuated<FnArg, syn::token::Comma>,
    generics: &mut Generics,
) {
    if let Some(FnArg::Receiver(recv)) = inputs.first_mut() {
        if let Some((_, ref mut lt_opt)) = recv.reference {
            if lt_opt.is_none() {
                let lt = fresh_lifetime(generics);
                *lt_opt = Some(lt.clone());
                insert_lifetime_param(generics, lt);
            }
        }
    }
}

/// Returns the full receiver type: `Self`, `&'a Self`, or `&'a mut Self`.
fn receiver_full_type(recv: &syn::Receiver) -> Type {
    match &recv.reference {
        None => syn::parse_quote!(Self),
        Some((_, Some(lt))) => {
            if recv.mutability.is_some() {
                syn::parse_quote!(&#lt mut Self)
            } else {
                syn::parse_quote!(&#lt Self)
            }
        }
        Some((_, None)) => {
            if recv.mutability.is_some() {
                syn::parse_quote!(&mut Self)
            } else {
                syn::parse_quote!(&Self)
            }
        }
    }
}

/// Returns `<ReceiverTy as Model>::Ty` — the model-type of the receiver.
fn receiver_model_ty(recv: &syn::Receiver) -> Type {
    let recv_ty = receiver_full_type(recv);
    syn::parse_quote!(<#recv_ty as thrust_models::Model>::Ty)
}

/// Rewrites every `self` ident in `expr` to `self_`.
fn rewrite_self_in_expr(expr: &syn::Expr) -> syn::Expr {
    struct RewriteSelf;
    impl VisitMut for RewriteSelf {
        fn visit_ident_mut(&mut self, i: &mut syn::Ident) {
            if i == "self" {
                *i = format_ident!("self_");
            }
        }
    }
    let mut e = expr.clone();
    RewriteSelf.visit_expr_mut(&mut e);
    e
}

/// Inserts fresh lifetimes into reference-typed params that have no explicit lifetime.
/// Mutates `inputs` (the type in-place) and `generics` (adds LifetimeParam).
/// Skips receiver params — handled by elaborate_receiver_lifetime.
fn elaborate_typed_param_lifetimes(
    inputs: &mut Punctuated<FnArg, syn::token::Comma>,
    generics: &mut Generics,
) {
    for arg in inputs.iter_mut() {
        let FnArg::Typed(pt) = arg else { continue };
        let Type::Reference(ref_ty) = pt.ty.as_mut() else {
            continue
        };
        if ref_ty.lifetime.is_some() {
            continue;
        }
        let lt = fresh_lifetime(generics);
        ref_ty.lifetime = Some(lt.clone());
        insert_lifetime_param(generics, lt);
    }
}

/// Returns the idents of type params that have Fn/FnOnce/FnMut bounds.
fn fn_has_fn_bounds(generics: &Generics) -> HashSet<String> {
    generics
        .params
        .iter()
        .filter_map(|p| {
            let GenericParam::Type(tp) = p else {
                return None;
            };
            let has_fn_bound = tp.bounds.iter().any(|b| {
                let TypeParamBound::Trait(tb) = b else {
                    return false;
                };
                tb.path.segments.last().map_or(false, |s| {
                    matches!(s.ident.to_string().as_str(), "Fn" | "FnOnce" | "FnMut")
                })
            });
            if has_fn_bound {
                Some(tp.ident.to_string())
            } else {
                None
            }
        })
        .collect()
}

/// Returns model where-predicates derived from actual parameter types.
/// For receivers: adds `ReceiverTy: Model` + `<ReceiverTy as Model>::Ty: PartialEq` (full type).
/// For typed params: recursively collects leaf type-variable idents and emits model predicates.
/// This catches type params from outer `impl<T>` blocks not present in the function's own generics.
/// Skips idents that match Fn-bound type params.
fn model_predicates_from_params(
    inputs: &Punctuated<FnArg, syn::token::Comma>,
    fn_bounds: &HashSet<String>,
) -> Vec<WherePredicate> {
    let mut seen = HashSet::new();
    let mut preds = Vec::new();
    for arg in inputs {
        match arg {
            FnArg::Receiver(recv) => {
                // For reference receivers use `Self: Model` rather than `&'a mut Self: Model`.
                // An explicit `&'a mut Self: Model` where clause blocks rustc's blanket impl
                // selection and causes normalization of `<&'a mut Self as Model>::Ty` to get
                // stuck. With `Self: Model` the solver can select the blanket impl and normalize.
                let inner_ty: Type = syn::parse_quote!(Self);
                let pred_ty = if recv.reference.is_some() { inner_ty } else { receiver_full_type(recv) };
                preds.push(syn::parse_quote!(#pred_ty: thrust_models::Model));
                preds.push(syn::parse_quote!(<#pred_ty as thrust_models::Model>::Ty: PartialEq));
            }
            FnArg::Typed(pt) => {
                collect_type_var_predicates(&pt.ty, fn_bounds, &mut seen, &mut preds);
            }
        }
    }
    preds
}

/// Recursively collects model where-predicates for every plain type-variable ident
/// reachable from `ty` (through references, tuples, and angle-bracketed generics).
fn collect_type_var_predicates(
    ty: &Type,
    fn_bounds: &HashSet<String>,
    seen: &mut HashSet<String>,
    preds: &mut Vec<WherePredicate>,
) {
    match ty {
        Type::Path(tp) if tp.qself.is_none() => {
            let segs = &tp.path.segments;
            if segs.len() == 1 && matches!(segs[0].arguments, syn::PathArguments::None) {
                // Plain ident — a type variable (or concrete type like i32; harmless either way).
                let name = segs[0].ident.to_string();
                if !fn_bounds.contains(&name) && seen.insert(name) {
                    let ident = &segs[0].ident;
                    preds.push(syn::parse_quote!(#ident: thrust_models::Model));
                    preds.push(syn::parse_quote!(<#ident as thrust_models::Model>::Ty: PartialEq));
                }
            } else {
                // Compound path (e.g. Option<T>, Vec<T>) — recurse into generic args.
                for seg in segs {
                    if let syn::PathArguments::AngleBracketed(args) = &seg.arguments {
                        for arg in &args.args {
                            if let syn::GenericArgument::Type(inner) = arg {
                                collect_type_var_predicates(inner, fn_bounds, seen, preds);
                            }
                        }
                    }
                }
            }
        }
        Type::Reference(ref_ty) => {
            collect_type_var_predicates(&ref_ty.elem, fn_bounds, seen, preds);
        }
        Type::Tuple(tuple_ty) => {
            for elem in &tuple_ty.elems {
                collect_type_var_predicates(elem, fn_bounds, seen, preds);
            }
        }
        _ => {}
    }
}

/// Builds `where <original predicates>, <model predicates>`.
/// Returns an empty token stream when both sets are empty.
fn extended_where_clause(generics: &Generics, model_preds: &[WherePredicate]) -> TokenStream2 {
    let existing: Vec<&WherePredicate> = generics
        .where_clause
        .as_ref()
        .map(|wc| wc.predicates.iter().collect())
        .unwrap_or_default();

    if existing.is_empty() && model_preds.is_empty() {
        return quote!();
    }

    quote! { where #(#existing,)* #(#model_preds),* }
}

/// Maps each function parameter to its model-type form for helper fn signatures.
/// Receiver → `self_: <ReceiverTy as Model>::Ty`; typed `x: T` → `x: <T as Model>::Ty`.
fn fn_params_with_model_ty(
    inputs: &Punctuated<FnArg, syn::token::Comma>,
) -> TokenStream2 {
    let params: Vec<TokenStream2> = inputs
        .iter()
        .filter_map(|arg| match arg {
            FnArg::Receiver(recv) => {
                let model_ty = receiver_model_ty(recv);
                Some(quote!(self_: #model_ty))
            }
            FnArg::Typed(pt) => {
                let pat = &pt.pat;
                let ty = &pt.ty;
                let model_ty: Type = syn::parse_quote!(<#ty as thrust_models::Model>::Ty);
                Some(quote!(#pat: #model_ty))
            }
        })
        .collect();
    quote!(#(#params),*)
}

/// For the extern_spec wrapper: replaces every typed parameter with a fresh `_arg_N` ident,
/// returning `(rewritten_inputs_tokens, call_args_tokens)`.
fn rewrite_inputs_for_call(
    inputs: &Punctuated<FnArg, syn::token::Comma>,
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
