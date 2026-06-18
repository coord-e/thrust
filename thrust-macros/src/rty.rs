//! Refinement-type annotations: `param`, `ret`, `sig`.
//!
//! Lowers refinement types (e.g. `List<{ v: i32 | v > 0 }>`) into
//! `#[thrust::formula_fn]`s plus `#[thrust::refinement_path(..)]` path
//! statements injected into the function body. The path identifies the
//! sub-type the formula applies to: `$i` selects the i-th parameter, `result`
//! the return slot, and a bare integer `i` the i-th generic argument.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};
use quote::{format_ident, quote};
use syn::{parse_macro_input, FnArg};

use crate::fn_outer_item::FnOuterItem;
use crate::spec::{
    extended_where_clause, generic_params_tokens, generic_turbofish, FnItemWithSignature,
};
use crate::{extract_outer_context, FormulaFnTypeLowering};

/// One step in a refinement's type-position path; mirrors the plugin's
/// `rty::TypePositionStep`. Encoded in `#[thrust::refinement_path(..)]` as
/// `Param(i)` → `$i`, `Return` → `result`, `TypeArg(i)` → `i`.
#[derive(Clone, Copy)]
enum TypePositionStep {
    Param(usize),
    Return,
    TypeArg(usize),
}

/// A `{ binder : ty | formula }` parsed from a type expression.
#[derive(Clone)]
struct RefinedType {
    binder: syn::Ident,
    binder_ty: TokenStream2,
    formula: TokenStream2,
}

/// A [`RefinedType`] together with the position where it applies.
#[derive(Clone)]
struct RefinedTypeAnnotation {
    position: Vec<TypePositionStep>,
    refined_type: RefinedType,
}

pub fn expand_param(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(func.attrs()) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let attr_tokens: Vec<TokenTree2> = TokenStream2::from(attr).into_iter().collect();
    let annotations = match collect_param_annotations(&func, &attr_tokens) {
        Ok(a) => a,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    expand_with_annotations(func, outer_context, annotations)
}

fn collect_param_annotations(
    func: &FnItemWithSignature,
    attr_tokens: &[TokenTree2],
) -> syn::Result<Vec<RefinedTypeAnnotation>> {
    let (name, ty_tokens) = parse_name_typed_binding(attr_tokens)?;
    let idx = param_index(func, &name)?;
    let (annotations, _) = parse_refined_type_annotations(&ty_tokens)?;
    Ok(anchor_at(annotations, TypePositionStep::Param(idx)))
}

pub fn expand_ret(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(func.attrs()) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let attr_tokens: Vec<TokenTree2> = TokenStream2::from(attr).into_iter().collect();
    let annotations = match collect_ret_annotations(&attr_tokens) {
        Ok(a) => a,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    expand_with_annotations(func, outer_context, annotations)
}

fn collect_ret_annotations(attr_tokens: &[TokenTree2]) -> syn::Result<Vec<RefinedTypeAnnotation>> {
    let (annotations, _) = parse_refined_type_annotations(attr_tokens)?;
    Ok(anchor_at(annotations, TypePositionStep::Return))
}

pub fn expand_sig(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as FnItemWithSignature);
    let outer_context = match extract_outer_context(func.attrs()) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    let attr_tokens: Vec<TokenTree2> = TokenStream2::from(attr).into_iter().collect();
    let annotations = match collect_sig_annotations(&func, &attr_tokens) {
        Ok(a) => a,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };
    expand_with_annotations(func, outer_context, annotations)
}

fn collect_sig_annotations(
    func: &FnItemWithSignature,
    attr_tokens: &[TokenTree2],
) -> syn::Result<Vec<RefinedTypeAnnotation>> {
    match attr_tokens.first() {
        Some(TokenTree2::Ident(id)) if id == "fn" => {}
        _ => return Err(err_tokens(attr_tokens, "expected `fn` in sig annotation")),
    }
    let arg_group = match attr_tokens.get(1) {
        Some(TokenTree2::Group(g)) if g.delimiter() == proc_macro2::Delimiter::Parenthesis => g,
        _ => return Err(err_tokens(attr_tokens, "expected `(..)` after `fn`")),
    };

    let mut annotations = Vec::new();
    let arg_tokens: Vec<TokenTree2> = arg_group.stream().into_iter().collect();
    for arg in split_top_level_commas(&arg_tokens) {
        if arg.is_empty() {
            continue;
        }
        let (name, ty_tokens) = parse_name_typed_binding(&arg)?;
        let idx = param_index(func, &name)?;
        let (param_annotations, _) = parse_refined_type_annotations(&ty_tokens)?;
        annotations.extend(anchor_at(param_annotations, TypePositionStep::Param(idx)));
    }

    let rest = &attr_tokens[2..];
    let ret_tokens = match (rest.first(), rest.get(1)) {
        (Some(TokenTree2::Punct(a)), Some(TokenTree2::Punct(b)))
            if a.as_char() == '-' && b.as_char() == '>' =>
        {
            &rest[2..]
        }
        _ => {
            return Err(err_tokens(
                attr_tokens,
                "expected `->` and a return type in sig annotation",
            ))
        }
    };
    let (ret_annotations, _) = parse_refined_type_annotations(ret_tokens)?;
    annotations.extend(anchor_at(ret_annotations, TypePositionStep::Return));
    Ok(annotations)
}

fn expand_with_annotations(
    mut func: FnItemWithSignature,
    outer_context: Option<FnOuterItem>,
    annotations: Vec<RefinedTypeAnnotation>,
) -> TokenStream {
    let has_receiver = func.sig().receiver().is_some();
    let mut formula_fns = Vec::new();
    let mut path_stmts = Vec::new();
    for mut annotation in annotations {
        if has_receiver {
            let self_ = format_ident!("self_");
            annotation.refined_type.formula = std::mem::take(&mut annotation.refined_type.formula)
                .into_iter()
                .map(|tt| crate::spec::rewrite_self_in_tokens(tt, &self_))
                .collect();
        }
        formula_fns.push(build_formula_fn(&func, outer_context.as_ref(), &annotation));
        path_stmts.push(build_refinement_path_stmt(&func, &annotation));
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

/// Parses the type expression in `tokens` and returns both the refined-type
/// annotations it contains (positioned relative to the start of `tokens`) and
/// the type expression as plain Rust tokens (with every refinement brace
/// replaced by the brace's binder type).
fn parse_refined_type_annotations(
    tokens: &[TokenTree2],
) -> syn::Result<(Vec<RefinedTypeAnnotation>, Vec<TokenTree2>)> {
    if tokens.is_empty() {
        return Ok((Vec::new(), Vec::new()));
    }

    // A refinement type `{ binder : ty | formula }`: emit one annotation here,
    // then descend into the binder type for any nested annotations. The
    // stripped form of the whole brace is the stripped form of the binder type.
    if tokens.len() == 1 {
        if let TokenTree2::Group(g) = &tokens[0] {
            if g.delimiter() == proc_macro2::Delimiter::Brace {
                let inner: Vec<TokenTree2> = g.stream().into_iter().collect();
                let bar = inner
                    .iter()
                    .position(|tt| matches!(tt, TokenTree2::Punct(p) if p.as_char() == '|'))
                    .ok_or_else(|| err_tokens(&inner, "refinement type must contain `|`"))?;
                let (binder, binder_ty_tokens) = parse_name_typed_binding(&inner[..bar])?;
                let formula: TokenStream2 = inner[bar + 1..].iter().cloned().collect();
                let (nested, stripped_binder_ty) =
                    parse_refined_type_annotations(&binder_ty_tokens)?;
                let mut out = vec![RefinedTypeAnnotation {
                    position: Vec::new(),
                    refined_type: RefinedType {
                        binder,
                        binder_ty: stripped_binder_ty.iter().cloned().collect(),
                        formula,
                    },
                }];
                out.extend(nested);
                return Ok((out, stripped_binder_ty));
            }
        }
    }

    // A reference `& [lifetime] [mut] T`: encoded by the plugin as a pointer,
    // so descend into the pointee at `TypeArg(0)`.
    if let Some(TokenTree2::Punct(p)) = tokens.first() {
        if p.as_char() == '&' {
            let mut cursor = 1;
            if let Some(TokenTree2::Punct(p)) = tokens.get(cursor) {
                if p.as_char() == '\'' {
                    cursor += 1;
                    if matches!(tokens.get(cursor), Some(TokenTree2::Ident(_))) {
                        cursor += 1;
                    }
                }
            }
            if matches!(tokens.get(cursor), Some(TokenTree2::Ident(id)) if id == "mut") {
                cursor += 1;
            }
            let (nested, stripped_pointee) = parse_refined_type_annotations(&tokens[cursor..])?;
            let mut stripped = tokens[..cursor].to_vec();
            stripped.extend(stripped_pointee);
            return Ok((anchor_at(nested, TypePositionStep::TypeArg(0)), stripped));
        }
    }

    // Anything else: scan past the qualifier tokens (path segments, `dyn`,
    // `impl`, …) to the first top-level `<`, then recurse into each generic
    // argument at `TypeArg(i)`. With no `<` there's nothing to descend into.
    let Some(lt) = tokens
        .iter()
        .position(|tt| matches!(tt, TokenTree2::Punct(p) if p.as_char() == '<'))
    else {
        return Ok((Vec::new(), tokens.to_vec()));
    };
    let mut out_annotations = Vec::new();
    let mut stripped = tokens[..=lt].to_vec();
    let mut type_idx = 0;
    for (i, arg) in split_angle_args(&tokens[lt + 1..]).into_iter().enumerate() {
        if i > 0 {
            stripped.push(TokenTree2::Punct(proc_macro2::Punct::new(
                ',',
                proc_macro2::Spacing::Alone,
            )));
        }
        if is_lifetime(&arg) {
            stripped.extend(arg);
            continue;
        }
        let (arg_annotations, stripped_arg) = parse_refined_type_annotations(&arg)?;
        out_annotations.extend(anchor_at(
            arg_annotations,
            TypePositionStep::TypeArg(type_idx),
        ));
        stripped.extend(stripped_arg);
        type_idx += 1;
    }
    stripped.push(TokenTree2::Punct(proc_macro2::Punct::new(
        '>',
        proc_macro2::Spacing::Alone,
    )));
    Ok((out_annotations, stripped))
}

/// Prepends `root` to every annotation's position.
fn anchor_at(
    mut annotations: Vec<RefinedTypeAnnotation>,
    root: TypePositionStep,
) -> Vec<RefinedTypeAnnotation> {
    for annotation in &mut annotations {
        annotation.position.insert(0, root);
    }
    annotations
}

/// Parses `name : <type tokens>` into the bound name and the type tokens.
fn parse_name_typed_binding(tokens: &[TokenTree2]) -> syn::Result<(syn::Ident, Vec<TokenTree2>)> {
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

/// Splits tokens after an opening `<` by top-level commas, stopping at the
/// matching `>`.
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

fn param_index(func: &FnItemWithSignature, name: &syn::Ident) -> syn::Result<usize> {
    let pos = func.sig().inputs.iter().position(|arg| match arg {
        FnArg::Receiver(_) => name == "self",
        FnArg::Typed(pt) => matches!(&*pt.pat, syn::Pat::Ident(pi) if &pi.ident == name),
    });
    pos.ok_or_else(|| {
        syn::Error::new_spanned(name, format!("no parameter named `{}` in signature", name))
    })
}

fn formula_fn_name(func: &FnItemWithSignature, ann: &RefinedTypeAnnotation) -> syn::Ident {
    let pos = ann
        .position
        .iter()
        .map(|s| match s {
            TypePositionStep::Param(i) => format!("p{}", i),
            TypePositionStep::Return => "ret".to_string(),
            TypePositionStep::TypeArg(i) => format!("t{}", i),
        })
        .collect::<Vec<_>>()
        .join("_");
    format_ident!("_thrust_refine_{}_{}", func.sig().ident, pos)
}

/// The `#[thrust::formula_fn]` declaration carrying the annotation's formula.
/// Its first parameter is the refined type's value binder; the rest are the
/// enclosing function's parameters in model-typed form.
fn build_formula_fn(
    func: &FnItemWithSignature,
    outer_context: Option<&FnOuterItem>,
    ann: &RefinedTypeAnnotation,
) -> TokenStream2 {
    let name = formula_fn_name(func, ann);
    let def_generics = generic_params_tokens(&func.sig().generics);
    let type_lowering = if let Some(outer_context) = outer_context {
        FormulaFnTypeLowering::with_outer_context(func.sig(), outer_context)
    } else {
        FormulaFnTypeLowering::new(func.sig())
    };
    let model_params = type_lowering.lower_params(&func.sig().inputs);
    let model_preds = type_lowering.model_where_predicates();
    let extended_where = extended_where_clause(func, &model_preds);
    let binder = &ann.refined_type.binder;
    let binder_ty = &ann.refined_type.binder_ty;
    let formula = crate::formula::wrap_expr(ann.refined_type.formula.clone());

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

/// The `#[thrust::refinement_path(..)] <fn>;` statement linking the generated
/// formula_fn to the annotation's position.
fn build_refinement_path_stmt(
    func: &FnItemWithSignature,
    ann: &RefinedTypeAnnotation,
) -> TokenStream2 {
    let name = formula_fn_name(func, ann);
    let turbofish = generic_turbofish(&func.sig().generics);
    let path_prefix = if func.sig().receiver().is_some() {
        quote!(Self::)
    } else {
        quote!()
    };
    let encoded_steps = ann.position.iter().map(|s| match s {
        TypePositionStep::Param(i) => {
            let lit = proc_macro2::Literal::usize_unsuffixed(*i);
            quote!($#lit)
        }
        TypePositionStep::Return => quote!(result),
        TypePositionStep::TypeArg(i) => {
            let lit = proc_macro2::Literal::usize_unsuffixed(*i);
            quote!(#lit)
        }
    });
    quote! {
        #[thrust::refinement_path(#(#encoded_steps),*)]
        #path_prefix #name #turbofish;
    }
}
