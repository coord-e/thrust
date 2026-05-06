use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, punctuated::Punctuated, FnArg, GenericParam, Generics, ItemFn, ReturnType,
    Type, TypeParamBound, WherePredicate,
};

#[proc_macro_attribute]
pub fn context(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut impl_item = syn::parse_macro_input!(item as syn::ItemImpl);
    let impl_header = {
        let mut header = impl_item.clone();
        header.items.clear();
        header
    };
    for item in &mut impl_item.items {
        let syn::ImplItem::Fn(item) = item else {
            continue;
        };
        // TODO: why ::thrust_macros doesn't work here?
        item.attrs
            .push(syn::parse_quote!(#[thrust::_impl_context(#impl_header)]));
    }
    impl_item.into_token_stream().into()
}

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);
    let mut func = parse_macro_input!(item as ItemFn);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs.push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures((#req_expr) && (#expr), #ens_expr)]
    ));

    func.into_token_stream().into()
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    let expr = TokenStream2::from(attr);
    let mut func = parse_macro_input!(item as ItemFn);

    let (req_expr, ens_expr) = match extract_requires_ensures(&mut func) {
        Ok((req, ens)) => (req, ens),
        Err(e) => return e.to_compile_error().into(),
    };
    func.attrs.push(syn::parse_quote!(
        #[::thrust_macros::_requires_ensures(#req_expr, (#ens_expr) && (#expr))]
    ));

    func.into_token_stream().into()
}

fn extract_requires_ensures(func: &mut ItemFn) -> syn::Result<(syn::Expr, syn::Expr)> {
    let mut result = None;

    let requires_ensures_path: syn::Path = syn::parse_quote!(::thrust_macros::_requires_ensures);

    for attr in &func.attrs {
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

    func.attrs
        .retain(|attr| attr.path() != &requires_ensures_path);

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

    let func = parse_macro_input!(item as ItemFn);
    let impl_context = match extract_impl_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => return e.to_compile_error().into(),
    };
    if mentions_self(&func.sig) && impl_context.is_none() {
        let err = syn::Error::new_spanned(
            func.sig.ident.clone(),
            "Wrap impl block with #[thrust_macros::context] to use requires/ensures on methods",
        )
        .to_compile_error();
        return quote! { #err #func }.into();
    }
    let mut tokens = ExpandedTokens::new(func, req_expr, ens_expr);
    if let Some(ctx) = impl_context {
        tokens = tokens.with_impl_context(ctx);
    }
    tokens.into_token_stream().into()
}

fn extract_impl_context(func: &syn::ItemFn) -> syn::Result<Option<syn::ItemImpl>> {
    let impl_context_path: syn::Path = syn::parse_quote!(thrust::_impl_context);
    let mut impl_context = None;
    for attr in &func.attrs {
        if attr.path() != &impl_context_path {
            continue;
        }

        let item = attr.parse_args()?;
        if impl_context.is_some() {
            return Err(syn::Error::new_spanned(
                attr,
                "multiple _impl_context attributes found; expected at most one",
            ));
        }
        impl_context = Some(item);
    }
    Ok(impl_context)
}

struct ExpandedTokens {
    func: ItemFn,

    requires_name: syn::Ident,
    ensures_name: syn::Ident,
    req_expr: syn::Expr,
    ens_expr: syn::Expr,

    def_generics: TokenStream2,
    turbofish: TokenStream2,
    extended_where: TokenStream2,

    model_ty_params: TokenStream2,
    ret_model_ty: Type,

    impl_context: Option<syn::ItemImpl>,
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
    pub fn new(func: ItemFn, req_expr: syn::Expr, ens_expr: syn::Expr) -> Self {
        let name = &func.sig.ident;
        let requires_name = format_ident!("_thrust_requires_{}", name);
        let ensures_name = format_ident!("_thrust_ensures_{}", name);

        let generics = &func.sig.generics;
        let def_generics = generic_params_tokens(generics);
        let turbofish = generic_turbofish(generics);
        let model_preds = model_where_predicates(generics);
        let extended_where = extended_where_clause(generics, &model_preds);

        let model_ty_params = fn_params_with_model_ty(&func.sig.inputs);
        let ret_model_ty: Type = match &func.sig.output {
            ReturnType::Default => syn::parse_quote!(<() as thrust_models::Model>::Ty),
            ReturnType::Type(_, ty) => syn::parse_quote!(<#ty as thrust_models::Model>::Ty),
        };

        Self {
            func,
            req_expr,
            ens_expr,
            requires_name,
            ensures_name,
            def_generics,
            turbofish,
            extended_where,
            model_ty_params,
            ret_model_ty,
            impl_context: None,
        }
    }

    pub fn with_impl_context(mut self, impl_item: syn::ItemImpl) -> Self {
        self.impl_context = Some(impl_item);
        self
    }

    fn is_extern_spec_fn(&self) -> bool {
        let extern_spec_fn_path: syn::Path = syn::parse_quote!(thrust::extern_spec_fn);
        self.func
            .attrs
            .iter()
            .any(|a| a.path() == &extern_spec_fn_path)
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
        let mut func = self.func.clone();
        let trusted_path: syn::Path = syn::parse_quote!(thrust::trusted);
        for attr in &mut func.attrs {
            if attr.path() == &trusted_path {
                *attr = syn::parse_quote!(#[thrust::ignored]);
            }
        }

        let requires_fn = self.requires_fn();
        let ensures_fn = self.ensures_fn();

        let extern_spec_name = format_ident!("_thrust_extern_spec_{}", self.func.sig.ident);
        let def_generics = &self.def_generics;
        let orig_output = &self.func.sig.output;
        let extended_where = &self.extended_where;

        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;

        let name = &self.func.sig.ident;
        let (extern_spec_inputs, call_args) = rewrite_inputs_for_call(&self.func.sig.inputs);

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

    fn expand_extern_spec_fn(&self) -> TokenStream2 {
        let requires_name = &self.requires_name;
        let ensures_name = &self.ensures_name;
        let turbofish = &self.turbofish;

        let mut func = self.func.clone();
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

/// Returns `T: thrust_models::Model` predicates for every type param that does not
/// already carry an `Fn`, `FnOnce`, or `FnMut` bound.
fn model_where_predicates(generics: &Generics) -> Vec<WherePredicate> {
    generics
        .params
        .iter()
        .flat_map(|p| {
            let GenericParam::Type(tp) = p else {
                return vec![];
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
                return vec![];
            }
            let ident = &tp.ident;
            vec![
                syn::parse_quote!(#ident: thrust_models::Model),
                syn::parse_quote!(<#ident as thrust_models::Model>::Ty: PartialEq),
            ]
        })
        .collect()
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

/// Maps each typed function parameter `x: T` to `x: <T as thrust_models::Model>::Ty`.
/// Receiver (`self`) parameters are skipped.
fn fn_params_with_model_ty(
    inputs: &syn::punctuated::Punctuated<FnArg, syn::token::Comma>,
) -> TokenStream2 {
    let params: Vec<TokenStream2> = inputs
        .iter()
        .filter_map(|arg| {
            let FnArg::Typed(pt) = arg else { return None };
            let pat = &pt.pat;
            let ty = &pt.ty;
            let model_ty: Type = syn::parse_quote!(<#ty as thrust_models::Model>::Ty);
            Some(quote!(#pat: #model_ty))
        })
        .collect();
    quote!(#(#params),*)
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
