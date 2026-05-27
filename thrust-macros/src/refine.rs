//! Refinement-type annotations: `param`, `ret`, `sig`.
//!
//! These lower refinement types (e.g. `List<{ v: i32 | v > 0 }>`) into
//! `#[thrust::formula_fn]`s plus positioned `#[thrust::refinement_path(..)]`
//! path statements injected into the function body. The "type position"
//! addresses into the function type: a parameter (by index) or the return (the
//! `result` keyword) selects a function slot, and bracket steps (`[i]`) descend
//! into generic arguments (enum args / `Box` pointee). For example,
//! `#[thrust::refinement_path(result, [0])]` is the first type-argument of the
//! return.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, FnArg};

use super::{
    extended_where_clause, extract_outer_context, fn_params_with_model_ty, generic_params_tokens,
    generic_turbofish, model_where_predicates, FnItemWithSignature, FnOuterItem,
};

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

pub(crate) enum RefineKind {
    Param,
    Ret,
    Sig,
}

pub(crate) fn expand_refine(kind: RefineKind, attr: TokenStream, item: TokenStream) -> TokenStream {
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
