use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse_macro_input, punctuated::Punctuated, FnArg, GenericParam, Generics, TypeParamBound,
    WherePredicate,
};

#[derive(Debug, Clone)]
enum FnOuterItem {
    ItemImpl(syn::ItemImpl),
    ItemTrait(syn::ItemTrait),
}

impl syn::parse::Parse for FnOuterItem {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        use syn::parse::discouraged::Speculative as _;

        let fork = input.fork();
        if let Ok(item_impl) = fork.parse::<syn::ItemImpl>() {
            input.advance_to(&fork);
            return Ok(Self::ItemImpl(item_impl));
        }

        let fork = input.fork();
        if let Ok(item_trait) = fork.parse::<syn::ItemTrait>() {
            input.advance_to(&fork);
            return Ok(Self::ItemTrait(item_trait));
        }

        Err(input.error("expected an impl block or a trait definition"))
    }
}

impl quote::ToTokens for FnOuterItem {
    fn to_tokens(&self, tokens: &mut TokenStream2) {
        match self {
            FnOuterItem::ItemImpl(item_impl) => item_impl.to_tokens(tokens),
            FnOuterItem::ItemTrait(item_trait) => item_trait.to_tokens(tokens),
        }
    }
}

impl FnOuterItem {
    fn into_header_only(mut self) -> Self {
        match &mut self {
            FnOuterItem::ItemImpl(item_impl) => {
                item_impl.items.clear();
            }
            FnOuterItem::ItemTrait(item_trait) => {
                item_trait.items.clear();
            }
        }
        self
    }

    fn generics(&self) -> &Generics {
        match self {
            FnOuterItem::ItemImpl(item_impl) => &item_impl.generics,
            FnOuterItem::ItemTrait(item_trait) => &item_trait.generics,
        }
    }
}

#[proc_macro_attribute]
pub fn context(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut outer_item = syn::parse_macro_input!(item as FnOuterItem);
    let outer_header = outer_item.clone().into_header_only();
    match &mut outer_item {
        FnOuterItem::ItemImpl(item_impl) => {
            for item in &mut item_impl.items {
                let syn::ImplItem::Fn(item) = item else {
                    continue;
                };
                item.attrs
                    .push(syn::parse_quote!(#[thrust::_outer_context(#outer_header)]));
            }
        }
        FnOuterItem::ItemTrait(item_trait) => {
            for item in &mut item_trait.items {
                let syn::TraitItem::Fn(item) = item else {
                    continue;
                };
                item.attrs
                    .push(syn::parse_quote!(#[thrust::_outer_context(#outer_header)]));
            }
        }
    }

    outer_item.into_token_stream().into()
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

#[proc_macro_attribute]
pub fn predicate(_attr: TokenStream, item: TokenStream) -> TokenStream {
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
    let model_ty_params = fn_params_with_model_ty(&func.sig().inputs);
    let model_ret = fn_return_ty_with_model_ty(&func.sig().output);

    let model_preds = model_where_predicates(&func, outer_context.as_ref());
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

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
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

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
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

fn extract_outer_context(func: &FnItemWithSignature) -> syn::Result<Option<FnOuterItem>> {
    let outer_context_path: syn::Path = syn::parse_quote!(thrust::_outer_context);
    let mut outer_context = None;
    for attr in func.attrs() {
        if attr.path() != &outer_context_path {
            continue;
        }

        let item = attr.parse_args()?;
        if outer_context.is_some() {
            return Err(syn::Error::new_spanned(
                attr,
                "multiple _outer_context attributes found; expected at most one",
            ));
        }
        outer_context = Some(item);
    }
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

    model_ty_params: TokenStream2,
    ret_model_ty: syn::Type,

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
    pub fn new(
        func: FnItemWithSignature,
        mut req_expr: syn::Expr,
        mut ens_expr: syn::Expr,
    ) -> Self {
        let name = &func.sig().ident;
        let requires_name = format_ident!("_thrust_requires_{}", name);
        let ensures_name = format_ident!("_thrust_ensures_{}", name);

        let generics = &func.sig().generics;
        let def_generics = generic_params_tokens(generics);
        let turbofish = generic_turbofish(generics);

        let model_ty_params = fn_params_with_model_ty(&func.sig().inputs);
        let ret_model_ty = fn_return_ty_with_model_ty(&func.sig().output);

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
            model_ty_params,
            ret_model_ty,
            outer_context: None,
        }
    }

    pub fn with_outer_context(mut self, outer_item: FnOuterItem) -> Self {
        self.outer_context = Some(outer_item);
        self
    }

    fn extended_where_clause(&self) -> TokenStream2 {
        let model_preds = model_where_predicates(&self.func, self.outer_context.as_ref());
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
        let model_ty_params = &self.model_ty_params;
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
        let model_ty_params = &self.model_ty_params;
        let extended_where = self.extended_where_clause();
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

// ---------------------------------------------------------------------------
// Refinement-type annotations: `param`, `ret`, `sig`.
//
// These lower refinement types (e.g. `List<{ v: i32 | v > 0 }>`) into
// `#[thrust::formula_fn]`s plus positioned `#[thrust::refinement_path(..)]`
// path statements injected into the function body. The "type position"
// addresses into the function type: a parameter (by index) or the return (the
// `result` keyword) selects a function slot, and bracket steps (`[i]`) descend
// into generic arguments (enum args / `Box` pointee). For example,
// `#[thrust::refinement_path(result, [0])]` is the first type-argument of the
// return.
// ---------------------------------------------------------------------------

/// One step in a refinement's type-position path.
///
/// Mirrors [`rty::TypePositionStep`] on the plugin side and uses the same
/// attribute encoding:
/// - [`Param`](Self::Param) / [`Return`](Self::Return) navigate into a function
///   type; encoded as an integer literal / the `result` keyword.
/// - [`TypeArg`](Self::TypeArg) navigates into a generic type argument; encoded
///   as a bracket group `[i]`.
#[derive(Clone, Copy)]
enum RefineStep {
    Param(usize),
    Return,
    TypeArg(usize),
}

#[derive(Clone)]
struct Refinement {
    /// Full type-position path from the function root to the refined type.
    steps: Vec<RefineStep>,
    binder: syn::Ident,
    binder_ty: TokenStream2,
    formula: TokenStream2,
}

#[proc_macro_attribute]
pub fn param(attr: TokenStream, item: TokenStream) -> TokenStream {
    expand_refine(RefineKind::Param, attr, item)
}

#[proc_macro_attribute]
pub fn ret(attr: TokenStream, item: TokenStream) -> TokenStream {
    expand_refine(RefineKind::Ret, attr, item)
}

#[proc_macro_attribute]
pub fn sig(attr: TokenStream, item: TokenStream) -> TokenStream {
    expand_refine(RefineKind::Sig, attr, item)
}

enum RefineKind {
    Param,
    Ret,
    Sig,
}

fn expand_refine(kind: RefineKind, attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let attr_tokens: Vec<TokenTree2> = TokenStream2::from(attr).into_iter().collect();
    let jobs = match build_refine_jobs(kind, &func, &attr_tokens) {
        Ok(jobs) => jobs,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let mut refinements = Vec::new();
    for (root_steps, ty_tokens) in jobs {
        if let Err(e) = scan_type(&ty_tokens, root_steps, &mut refinements) {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    }

    if refinements.is_empty() {
        return func.into_token_stream().into();
    }

    let has_receiver = func.sig().receiver().is_some();
    let mut formula_fns = Vec::new();
    let mut path_stmts = Vec::new();
    for mut r in refinements {
        if has_receiver {
            r.formula = rewrite_self_in_tokens(r.formula);
        }
        formula_fns.push(refine_formula_fn(&func, outer_context.as_ref(), &r));
        path_stmts.push(refine_path_stmt(&func, &r));
    }

    let Some(block) = func.block_mut() else {
        let err = syn::Error::new_spanned(
            func.sig().ident.clone(),
            "refinement-type annotations require a function body",
        )
        .into_compile_error();
        return quote! { #err #func }.into();
    };
    let orig_stmts = block.stmts.drain(..).collect::<Vec<_>>();
    *block = syn::parse_quote!({
        #(#path_stmts)*
        #(#orig_stmts)*
    });
    func.attrs_mut()
        .push(syn::parse_quote!(#[allow(path_statements)]));

    quote! {
        #(#formula_fns)*
        #func
    }
    .into()
}

/// Builds `(root_steps, type_tokens)` jobs to scan from the attribute tokens.
///
/// Each job's `root_steps` contains the initial [`RefineStep`]s that fix the
/// position of the type expression within the function signature (e.g.
/// `[Param(0)]` for the first parameter).  [`scan_type`] will append further
/// [`RefineStep::TypeArg`] steps as it descends into generic type arguments.
fn build_refine_jobs(
    kind: RefineKind,
    func: &FnItemWithSignature,
    attr_tokens: &[TokenTree2],
) -> syn::Result<Vec<(Vec<RefineStep>, Vec<TokenTree2>)>> {
    match kind {
        RefineKind::Param => {
            let (name, ty_tokens) = split_name_type(attr_tokens)?;
            let idx = param_index(func, &name)?;
            Ok(vec![(vec![RefineStep::Param(idx)], ty_tokens)])
        }
        RefineKind::Ret => Ok(vec![(vec![RefineStep::Return], attr_tokens.to_vec())]),
        RefineKind::Sig => {
            let (args, ret_tokens) = parse_sig_attr(attr_tokens)?;
            let mut jobs = Vec::new();
            for (name, ty_tokens) in args {
                let idx = param_index(func, &name)?;
                jobs.push((vec![RefineStep::Param(idx)], ty_tokens));
            }
            jobs.push((vec![RefineStep::Return], ret_tokens));
            Ok(jobs)
        }
    }
}

fn param_index(func: &FnItemWithSignature, name: &syn::Ident) -> syn::Result<usize> {
    let pos = func.sig().inputs.iter().position(|arg| match arg {
        FnArg::Receiver(_) => name == "self",
        FnArg::Typed(pt) => matches!(&*pt.pat, syn::Pat::Ident(pi) if &pi.ident == name),
    });
    pos.ok_or_else(|| {
        syn::Error::new_spanned(name, format!("no parameter named `{}` in signature", name))
    })
}

/// Parses `name : <type tokens>` from a flat token slice.
fn split_name_type(tokens: &[TokenTree2]) -> syn::Result<(syn::Ident, Vec<TokenTree2>)> {
    let name = match tokens.first() {
        Some(TokenTree2::Ident(id)) => id.clone(),
        _ => return Err(err_tokens(tokens, "expected a parameter name")),
    };
    match tokens.get(1) {
        Some(TokenTree2::Punct(p)) if p.as_char() == ':' => {}
        _ => return Err(err_tokens(tokens, "expected `:` after parameter name")),
    }
    Ok((name, tokens[2..].to_vec()))
}

/// Parses `fn ( n0: t0 , ... ) -> ret` into `((name, ty_tokens)*, ret_tokens)`.
#[allow(clippy::type_complexity)]
fn parse_sig_attr(
    tokens: &[TokenTree2],
) -> syn::Result<(Vec<(syn::Ident, Vec<TokenTree2>)>, Vec<TokenTree2>)> {
    match tokens.first() {
        Some(TokenTree2::Ident(id)) if id == "fn" => {}
        _ => return Err(err_tokens(tokens, "expected `fn` in sig annotation")),
    }
    let arg_group = match tokens.get(1) {
        Some(TokenTree2::Group(g)) if g.delimiter() == proc_macro2::Delimiter::Parenthesis => g,
        _ => return Err(err_tokens(tokens, "expected `(..)` after `fn`")),
    };

    let mut args = Vec::new();
    let arg_tokens: Vec<TokenTree2> = arg_group.stream().into_iter().collect();
    for arg in split_top_level_commas(&arg_tokens) {
        if arg.is_empty() {
            continue;
        }
        args.push(split_name_type(&arg)?);
    }

    // expect `->` then the return type
    let mut rest = &tokens[2..];
    match (rest.first(), rest.get(1)) {
        (Some(TokenTree2::Punct(a)), Some(TokenTree2::Punct(b)))
            if a.as_char() == '-' && b.as_char() == '>' =>
        {
            rest = &rest[2..];
        }
        _ => {
            return Err(err_tokens(
                tokens,
                "expected `->` and a return type in sig annotation",
            ))
        }
    }
    Ok((args, rest.to_vec()))
}

/// Scans a type expression and records every refinement node with its full
/// type-position path (`steps`).
///
/// `steps` holds the path from the function root to the current type node.
/// When a refinement `{binder: ty | formula}` is found the current `steps` are
/// recorded; when descending into generic type arguments a
/// [`RefineStep::TypeArg`]`(i)` step is appended to `steps`.
fn scan_type(
    tokens: &[TokenTree2],
    steps: Vec<RefineStep>,
    out: &mut Vec<Refinement>,
) -> syn::Result<()> {
    if tokens.is_empty() {
        return Ok(());
    }

    // A refinement node is exactly a brace-delimited group.
    if tokens.len() == 1 {
        if let TokenTree2::Group(g) = &tokens[0] {
            if g.delimiter() == proc_macro2::Delimiter::Brace {
                let (binder, binder_ty, formula) = split_refinement(g.stream())?;
                out.push(Refinement {
                    steps: steps.clone(),
                    binder,
                    binder_ty: binder_ty.iter().cloned().collect(),
                    formula,
                });
                // Descend into the binder type for nested refinements.
                scan_type(&binder_ty, steps, out)?;
                return Ok(());
            }
        }
    }

    // A nominal type `Name<arg0, arg1, ..>` (`Box` included).
    if let TokenTree2::Ident(_) = &tokens[0] {
        if let Some(TokenTree2::Punct(p)) = tokens.get(1) {
            if p.as_char() == '<' {
                let mut type_idx = 0;
                for arg in split_angle_args(&tokens[2..]) {
                    if is_lifetime(&arg) {
                        continue;
                    }
                    let mut child = steps.clone();
                    child.push(RefineStep::TypeArg(type_idx));
                    scan_type(&arg, child, out)?;
                    type_idx += 1;
                }
            }
        }
    }

    Ok(())
}

/// Splits `{ binder : ty | formula }` contents into its parts.
fn split_refinement(
    stream: TokenStream2,
) -> syn::Result<(syn::Ident, Vec<TokenTree2>, TokenStream2)> {
    let toks: Vec<TokenTree2> = stream.into_iter().collect();
    let bar = toks
        .iter()
        .position(|tt| matches!(tt, TokenTree2::Punct(p) if p.as_char() == '|'))
        .ok_or_else(|| err_tokens(&toks, "refinement type must contain `|`"))?;
    let (binder, binder_ty) = split_name_type(&toks[..bar])?;
    let formula: TokenStream2 = toks[bar + 1..].iter().cloned().collect();
    Ok((binder, binder_ty, formula))
}

/// Splits the tokens following an opening `<` at top level by commas, stopping
/// at the matching `>`.
fn split_angle_args(tokens: &[TokenTree2]) -> Vec<Vec<TokenTree2>> {
    let mut args = Vec::new();
    let mut cur = Vec::new();
    let mut depth = 1usize;
    for tt in tokens {
        if let TokenTree2::Punct(p) = tt {
            match p.as_char() {
                '<' => {
                    depth += 1;
                    cur.push(tt.clone());
                    continue;
                }
                '>' => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                    cur.push(tt.clone());
                    continue;
                }
                ',' if depth == 1 => {
                    args.push(std::mem::take(&mut cur));
                    continue;
                }
                _ => {}
            }
        }
        cur.push(tt.clone());
    }
    if !cur.is_empty() {
        args.push(cur);
    }
    args
}

fn split_top_level_commas(tokens: &[TokenTree2]) -> Vec<Vec<TokenTree2>> {
    let mut out = Vec::new();
    let mut cur = Vec::new();
    let mut depth = 0i32;
    for tt in tokens {
        if let TokenTree2::Punct(p) = tt {
            match p.as_char() {
                '<' => depth += 1,
                '>' => depth -= 1,
                ',' if depth == 0 => {
                    out.push(std::mem::take(&mut cur));
                    continue;
                }
                _ => {}
            }
        }
        cur.push(tt.clone());
    }
    out.push(cur);
    out
}

fn is_lifetime(tokens: &[TokenTree2]) -> bool {
    matches!(tokens.first(), Some(TokenTree2::Punct(p)) if p.as_char() == '\'')
}

fn err_tokens(tokens: &[TokenTree2], msg: &str) -> syn::Error {
    let stream: TokenStream2 = tokens.iter().cloned().collect();
    syn::Error::new_spanned(stream, msg)
}

fn rewrite_self_in_tokens(tokens: TokenStream2) -> TokenStream2 {
    tokens
        .into_iter()
        .map(|tt| match tt {
            TokenTree2::Ident(id) if id == "self" => TokenTree2::Ident(format_ident!("self_")),
            TokenTree2::Group(g) => {
                let inner = rewrite_self_in_tokens(g.stream());
                TokenTree2::Group(proc_macro2::Group::new(g.delimiter(), inner))
            }
            other => other,
        })
        .collect()
}

fn refine_fn_name(func: &FnItemWithSignature, r: &Refinement) -> syn::Ident {
    let pos = r
        .steps
        .iter()
        .map(|s| match s {
            RefineStep::Param(i) => format!("p{}", i),
            RefineStep::Return => "ret".to_string(),
            RefineStep::TypeArg(i) => format!("t{}", i),
        })
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("_thrust_refine_{}_{}", func.sig().ident, pos)
}

fn refine_formula_fn(
    func: &FnItemWithSignature,
    outer_context: Option<&FnOuterItem>,
    r: &Refinement,
) -> TokenStream2 {
    let name = refine_fn_name(func, r);
    let def_generics = generic_params_tokens(&func.sig().generics);
    let model_params = fn_params_with_model_ty(&func.sig().inputs);
    let model_preds = model_where_predicates(func, outer_context);
    let extended_where = extended_where_clause(func, &model_preds);
    let binder = &r.binder;
    let binder_ty = &r.binder_ty;
    let formula = &r.formula;

    quote! {
        #[allow(unused_variables)]
        #[allow(non_snake_case)]
        #[thrust::formula_fn]
        fn #name #def_generics(
            #binder: <#binder_ty as thrust_models::Model>::Ty,
            #model_params
        ) -> bool #extended_where {
            #formula
        }
    }
}

fn refine_path_stmt(func: &FnItemWithSignature, r: &Refinement) -> TokenStream2 {
    let name = refine_fn_name(func, r);
    let turbofish = generic_turbofish(&func.sig().generics);
    let path_prefix = if func.sig().receiver().is_some() {
        quote!(Self::)
    } else {
        quote!()
    };
    let encoded_steps = r.steps.iter().map(|s| match s {
        RefineStep::Param(i) => {
            let lit = proc_macro2::Literal::usize_unsuffixed(*i);
            quote!(#lit)
        }
        RefineStep::Return => quote!(result),
        RefineStep::TypeArg(i) => {
            let lit = proc_macro2::Literal::usize_unsuffixed(*i);
            quote!([#lit])
        }
    });
    quote! {
        #[thrust::refinement_path(#(#encoded_steps),*)]
        #path_prefix #name #turbofish;
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

/// Maps each function parameter `x: T` to `x: <T as thrust_models::Model>::Ty`.
fn fn_params_with_model_ty<'ast, I>(args: I) -> TokenStream2
where
    I: IntoIterator<Item = &'ast FnArg>,
{
    let mut model_inputs: Vec<FnArg> = Vec::new();
    for arg in args {
        match arg {
            FnArg::Receiver(receiver) => {
                let ty = &receiver.ty;
                model_inputs.push(syn::parse_quote!(self_: <#ty as thrust_models::Model>::Ty));
            }
            FnArg::Typed(pt) => {
                let pat = &pt.pat;
                let ty = &pt.ty;
                model_inputs.push(syn::parse_quote!(#pat: <#ty as thrust_models::Model>::Ty));
            }
        }
    }
    quote!(#(#model_inputs),*)
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

/// Returns `T: thrust_models::Model` predicates for every type param that does not
/// already carry an `Fn`, `FnOnce`, or `FnMut` bound.
fn model_where_predicates(
    func: &FnItemWithSignature,
    outer_context: Option<&FnOuterItem>,
) -> Vec<WherePredicate> {
    struct GenericTypeParam {
        ident: syn::Ident,
        bounds: Vec<TypeParamBound>,
    }

    impl From<syn::TypeParam> for GenericTypeParam {
        fn from(tp: syn::TypeParam) -> Self {
            Self {
                ident: tp.ident,
                bounds: tp.bounds.into_iter().collect(),
            }
        }
    }

    impl GenericTypeParam {
        fn has_fn_bound(&self) -> bool {
            self.bounds.iter().any(|b| {
                let TypeParamBound::Trait(tb) = b else {
                    return false;
                };
                tb.path.segments.last().is_some_and(|s| {
                    matches!(s.ident.to_string().as_str(), "Fn" | "FnOnce" | "FnMut")
                })
            })
        }
    }

    let mut generic_type_params: Vec<GenericTypeParam> = Vec::new();
    for param in &func.sig().generics.params {
        let GenericParam::Type(tp) = param else {
            continue;
        };
        generic_type_params.push(tp.clone().into());
    }
    if let Some(outer_item) = outer_context {
        for param in &outer_item.generics().params {
            let GenericParam::Type(tp) = param else {
                continue;
            };
            generic_type_params.push(tp.clone().into());
        }
        if let FnOuterItem::ItemTrait(outer_item) = &outer_item {
            generic_type_params.push(GenericTypeParam {
                ident: format_ident!("Self"),
                bounds: outer_item.supertraits.iter().cloned().collect(),
            });
        }
    }
    generic_type_params.retain(|p| !p.has_fn_bound());

    let mut predicates: Vec<WherePredicate> = Vec::new();
    for param in &generic_type_params {
        let ident = &param.ident;
        predicates.push(syn::parse_quote!(#ident: thrust_models::Model));
        predicates.push(syn::parse_quote!(<#ident as thrust_models::Model>::Ty: PartialEq));
    }

    struct Visitor {
        generic_type_params: Vec<GenericTypeParam>,
        generic_paths: Vec<syn::TypePath>,
    }

    impl syn::visit::Visit<'_> for Visitor {
        fn visit_type_path(&mut self, tp: &syn::TypePath) {
            for param in &self.generic_type_params {
                if let Some(qself) = &tp.qself {
                    let param = &param.ident;
                    let param_ty: syn::Type = syn::parse_quote!(#param);
                    if *qself.ty == param_ty {
                        self.generic_paths.push(tp.clone());
                    }
                }
                if tp.path.segments.len() > 1
                    && tp.path.segments.first().unwrap().ident == param.ident
                    && tp.qself.is_none()
                {
                    self.generic_paths.push(tp.clone());
                }
            }
            syn::visit::visit_type_path(self, tp);
        }
    }

    let mut visitor = Visitor {
        generic_type_params,
        generic_paths: Vec::new(),
    };
    use syn::visit::Visit as _;
    for arg in &func.sig().inputs {
        visitor.visit_fn_arg(arg);
    }
    visitor.visit_return_type(&func.sig().output);
    for tp in visitor.generic_paths {
        predicates.push(syn::parse_quote!(#tp: thrust_models::Model));
        predicates.push(syn::parse_quote!(<#tp as thrust_models::Model>::Ty: PartialEq));
    }

    predicates
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

fn fn_return_ty_with_model_ty(ret: &syn::ReturnType) -> syn::Type {
    match ret {
        syn::ReturnType::Default => syn::parse_quote!(<() as thrust_models::Model>::Ty),
        syn::ReturnType::Type(_, ty) => syn::parse_quote!(<#ty as thrust_models::Model>::Ty),
    }
}
