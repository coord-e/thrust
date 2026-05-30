//! Refinement-type annotations: `param`, `ret`, `sig`.
//!
//! These lower refinement types (e.g. `List<{ v: i32 | v > 0 }>`) into
//! `#[thrust::formula_fn]`s plus positioned `#[thrust::refinement_path(..)]`
//! path statements injected into the function body. The "type position"
//! addresses into the function type: a parameter (`$i`) or the return (the
//! `result` keyword) selects a function slot, and bare integer steps (`i`)
//! descend into generic arguments (enum args / `Box` pointee). For example,
//! `#[thrust::refinement_path(result, 0)]` is the first type-argument of the
//! return.

use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};
use quote::{format_ident, quote, ToTokens};
use syn::{parse_macro_input, FnArg};

use super::{
    extended_where_clause, extract_outer_context, fn_params_with_model_ty, generic_params_tokens,
    generic_turbofish, model_where_predicates, FnItemWithSignature, FnOuterItem,
};

/// One step in a refinement's type-position path; mirrors the plugin's
/// `rty::TypePositionStep`.
///
/// The attribute encoding emitted into `#[thrust::refinement_path(..)]` is:
/// `Param(i)` → `$i`, `Return` → `result`, `TypeArg(i)` → a bare integer `i`.
#[derive(Clone, Copy)]
enum TypePositionStep {
    Param(usize),
    Return,
    TypeArg(usize),
}

#[derive(Clone)]
struct Refinement {
    /// Full type-position path from the function root to the refined type.
    steps: Vec<TypePositionStep>,
    binder: syn::Ident,
    binder_ty: TokenStream2,
    formula: TokenStream2,
}

/// Which refinement-type annotation is being expanded.
pub(crate) enum AnnotationKind {
    Param,
    Ret,
    Sig,
}

/// A type expression from the annotation, paired with the position of its root
/// within the function signature. [`scan_type`] walks each one to extract the
/// refinements it contains.
struct PositionedTypeExpr {
    /// Steps locating the root of `tokens` (e.g. `[Param(0)]` for the first
    /// parameter); [`scan_type`] appends `TypeArg` steps as it descends.
    root: Vec<TypePositionStep>,
    tokens: Vec<TokenTree2>,
}

/// A `name : type` binding, e.g. a parameter in a `sig` annotation or the
/// binder of a refinement `{ name: type | .. }`.
struct NamedType {
    name: syn::Ident,
    tokens: Vec<TokenTree2>,
}

pub(crate) fn expand(kind: AnnotationKind, attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as FnItemWithSignature);

    let outer_context = match extract_outer_context(&func) {
        Ok(ctx) => ctx,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let attr_tokens: Vec<TokenTree2> = TokenStream2::from(attr).into_iter().collect();
    let type_exprs = match annotated_type_exprs(kind, &func, &attr_tokens) {
        Ok(exprs) => exprs,
        Err(e) => {
            let err = e.to_compile_error();
            return quote! { #err #func }.into();
        }
    };

    let mut refinements = Vec::new();
    for expr in type_exprs {
        if let Err(e) = scan_type(&expr.tokens, expr.root, &mut refinements) {
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

/// Turns an annotation into the type expressions to scan, each anchored at its
/// root position within the function signature.
fn annotated_type_exprs(
    kind: AnnotationKind,
    func: &FnItemWithSignature,
    attr_tokens: &[TokenTree2],
) -> syn::Result<Vec<PositionedTypeExpr>> {
    let at_param = |func: &FnItemWithSignature, nt: NamedType| -> syn::Result<PositionedTypeExpr> {
        let idx = param_index(func, &nt.name)?;
        Ok(PositionedTypeExpr {
            root: vec![TypePositionStep::Param(idx)],
            tokens: nt.tokens,
        })
    };
    match kind {
        AnnotationKind::Param => Ok(vec![at_param(func, split_name_type(attr_tokens)?)?]),
        AnnotationKind::Ret => Ok(vec![PositionedTypeExpr {
            root: vec![TypePositionStep::Return],
            tokens: attr_tokens.to_vec(),
        }]),
        AnnotationKind::Sig => {
            let sig = parse_sig_attr(attr_tokens)?;
            let mut exprs = Vec::new();
            for param in sig.params {
                exprs.push(at_param(func, param)?);
            }
            exprs.push(PositionedTypeExpr {
                root: vec![TypePositionStep::Return],
                tokens: sig.ret,
            });
            Ok(exprs)
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
fn split_name_type(tokens: &[TokenTree2]) -> syn::Result<NamedType> {
    let name = match tokens.first() {
        Some(TokenTree2::Ident(id)) => id.clone(),
        _ => return Err(err_tokens(tokens, "expected a parameter name")),
    };
    match tokens.get(1) {
        Some(TokenTree2::Punct(p)) if p.as_char() == ':' => {}
        _ => return Err(err_tokens(tokens, "expected `:` after parameter name")),
    }
    Ok(NamedType {
        name,
        tokens: tokens[2..].to_vec(),
    })
}

/// The parsed parts of a `fn ( n0: t0 , ... ) -> ret` signature annotation.
struct SigAnnotation {
    params: Vec<NamedType>,
    ret: Vec<TokenTree2>,
}

/// Parses `fn ( n0: t0 , ... ) -> ret`.
fn parse_sig_attr(tokens: &[TokenTree2]) -> syn::Result<SigAnnotation> {
    match tokens.first() {
        Some(TokenTree2::Ident(id)) if id == "fn" => {}
        _ => return Err(err_tokens(tokens, "expected `fn` in sig annotation")),
    }
    let arg_group = match tokens.get(1) {
        Some(TokenTree2::Group(g)) if g.delimiter() == proc_macro2::Delimiter::Parenthesis => g,
        _ => return Err(err_tokens(tokens, "expected `(..)` after `fn`")),
    };

    let mut params = Vec::new();
    let arg_tokens: Vec<TokenTree2> = arg_group.stream().into_iter().collect();
    for arg in split_top_level_commas(&arg_tokens) {
        if arg.is_empty() {
            continue;
        }
        params.push(split_name_type(&arg)?);
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
    Ok(SigAnnotation {
        params,
        ret: rest.to_vec(),
    })
}

/// Scans a type expression and records every refinement node with its full
/// type-position path (`steps`).
///
/// `steps` holds the path from the function root to the current type node.
/// When a refinement `{binder: ty | formula}` is found the current `steps` are
/// recorded; when descending into generic type arguments a
/// [`TypePositionStep::TypeArg`]`(i)` step is appended to `steps`.
fn scan_type(
    tokens: &[TokenTree2],
    steps: Vec<TypePositionStep>,
    out: &mut Vec<Refinement>,
) -> syn::Result<()> {
    if tokens.is_empty() {
        return Ok(());
    }

    // A refinement node is exactly a brace-delimited group.
    if tokens.len() == 1 {
        if let TokenTree2::Group(g) = &tokens[0] {
            if g.delimiter() == proc_macro2::Delimiter::Brace {
                let (binder, formula) = split_refinement(g.stream())?;
                out.push(Refinement {
                    steps: steps.clone(),
                    binder: binder.name,
                    binder_ty: binder.tokens.iter().cloned().collect(),
                    formula,
                });
                // Descend into the binder type for nested refinements.
                scan_type(&binder.tokens, steps, out)?;
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
                    child.push(TypePositionStep::TypeArg(type_idx));
                    scan_type(&arg, child, out)?;
                    type_idx += 1;
                }
            }
        }
    }

    Ok(())
}

/// Splits `{ binder : ty | formula }` into its binder and formula expression.
fn split_refinement(stream: TokenStream2) -> syn::Result<(NamedType, TokenStream2)> {
    let toks: Vec<TokenTree2> = stream.into_iter().collect();
    let bar = toks
        .iter()
        .position(|tt| matches!(tt, TokenTree2::Punct(p) if p.as_char() == '|'))
        .ok_or_else(|| err_tokens(&toks, "refinement type must contain `|`"))?;
    let binder = split_name_type(&toks[..bar])?;
    let formula: TokenStream2 = toks[bar + 1..].iter().cloned().collect();
    Ok((binder, formula))
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
            TypePositionStep::Param(i) => format!("p{}", i),
            TypePositionStep::Return => "ret".to_string(),
            TypePositionStep::TypeArg(i) => format!("t{}", i),
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
