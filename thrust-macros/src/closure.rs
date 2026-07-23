//! Expansion of `thrust_macros::closure!`, which attaches an explicit
//! `requires`/`ensures` specification to a closure expression.
//!
//! Rust attributes cannot sit on a closure *expression*, so the spec is written
//! as leading `requires(..)` / `ensures(..)` clauses in a wrapper macro:
//!
//! ```ignore
//! let f = thrust_macros::closure!(
//!     requires(x > 0),
//!     ensures(result == x + 1),
//!     |x: i32| -> i32 { x + 1 },
//! );
//! ```
//!
//! The expansion rewrites the closure so its body block gains, as leading
//! statements, `#[thrust::formula_fn]` companions plus `#[thrust::requires_path]`
//! / `#[thrust::ensures_path]` path statements — the exact same markers the
//! plugin already reads for named `fn` specs (see `spec.rs`). The plugin then
//! installs those formulas onto the closure's `FunctionType` in place of the
//! inferred predicate-variable templates. Each clause is optional: omit one and
//! that side stays inferred (a pvar). The closure header supplies the parameter
//! and return types, so nothing is restated.
//!
//! Generic/`Self` context threading (the `invariant_context` machinery) is not
//! supported here: closures in generic contexts that refer to generic- or
//! `Self`-typed values are out of scope for now.

use std::sync::atomic::{AtomicUsize, Ordering};

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::{format_ident, quote, ToTokens};
use syn::{
    parenthesized,
    parse::{Parse, ParseStream},
    FnArg,
};

use crate::FormulaFnTypeLowering;

mod kw {
    syn::custom_keyword!(requires);
    syn::custom_keyword!(ensures);
}

static COUNTER: AtomicUsize = AtomicUsize::new(0);

struct ClosureSpec {
    /// Preprocessed `requires` predicates (already run through `formula::expand`).
    requires: Vec<TokenStream2>,
    /// Preprocessed `ensures` predicates.
    ensures: Vec<TokenStream2>,
    closure: syn::ExprClosure,
}

impl Parse for ClosureSpec {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut requires = Vec::new();
        let mut ensures = Vec::new();

        loop {
            if input.peek(kw::requires) {
                input.parse::<kw::requires>()?;
                let content;
                parenthesized!(content in input);
                let raw: TokenStream2 = content.parse()?;
                requires.push(crate::formula::expand(raw));
            } else if input.peek(kw::ensures) {
                input.parse::<kw::ensures>()?;
                let content;
                parenthesized!(content in input);
                let raw: TokenStream2 = content.parse()?;
                ensures.push(crate::formula::expand(raw));
            } else {
                break;
            }
            input.parse::<Option<syn::Token![,]>>()?;
        }

        let closure: syn::ExprClosure = input.parse()?;
        input.parse::<Option<syn::Token![,]>>()?;

        Ok(Self {
            requires,
            ensures,
            closure,
        })
    }
}

pub fn expand(input: TokenStream) -> TokenStream {
    let spec = match syn::parse::<ClosureSpec>(input) {
        Ok(spec) => spec,
        Err(e) => return e.to_compile_error().into(),
    };
    match expand_closure(spec) {
        Ok(expr) => expr.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn expand_closure(spec: ClosureSpec) -> syn::Result<syn::ExprClosure> {
    let ClosureSpec {
        requires,
        ensures,
        mut closure,
    } = spec;

    // The closure parameters, restated as `fn` arguments so their types can be
    // lowered to model types.
    let mut fn_params: Vec<FnArg> = Vec::new();
    for param in &closure.inputs {
        let syn::Pat::Type(pt) = param else {
            return Err(syn::Error::new_spanned(
                param,
                "closure!'s closure parameters must have explicit types, e.g. `|x: i32| ...`",
            ));
        };
        let pat = &pt.pat;
        let ty = &pt.ty;
        fn_params.push(syn::parse_quote!(#pat: #ty));
    }

    if !ensures.is_empty() && matches!(closure.output, syn::ReturnType::Default) {
        return Err(syn::Error::new_spanned(
            &closure,
            "closure! with `ensures` must declare an explicit return type, e.g. `|x: i32| -> i32 { .. }`",
        ));
    }

    let dummy_sig: syn::Signature = syn::parse_quote!(fn __thrust_closure_spec());
    let type_lowering = FormulaFnTypeLowering::new(&dummy_sig);
    let model_params = type_lowering.lower_params(&fn_params);

    let id = COUNTER.fetch_add(1, Ordering::Relaxed);

    let mut prelude: Vec<TokenStream2> = Vec::new();

    if !requires.is_empty() {
        let name = format_ident!("_thrust_closure_requires_{}", id);
        let body = conjoin(&requires);
        prelude.push(quote! {
            #[allow(unused_variables, non_snake_case)]
            #[thrust::formula_fn]
            fn #name(#model_params) -> bool {
                #body
            }
        });
        prelude.push(quote! {
            #[thrust::requires_path]
            #name;
        });
    }

    if !ensures.is_empty() {
        let name = format_ident!("_thrust_closure_ensures_{}", id);
        let body = conjoin(&ensures);
        let ret_model = type_lowering.lower_return_type(&closure.output);
        prelude.push(quote! {
            #[allow(unused_variables, non_snake_case)]
            #[thrust::formula_fn]
            fn #name(result: #ret_model, #model_params) -> bool {
                #body
            }
        });
        prelude.push(quote! {
            #[thrust::ensures_path]
            #name;
        });
    }

    // Splice the prelude into the closure body. When the body is already a block,
    // prepend into it (rather than nesting a second block) so the tail expression
    // stays bare and no `unused_braces` warning is emitted.
    let prelude_block: syn::Block = syn::parse_quote!({ #(#prelude)* });
    let new_body: syn::Expr = match *closure.body {
        syn::Expr::Block(ref expr_block)
            if expr_block.attrs.is_empty() && expr_block.label.is_none() =>
        {
            let mut block = expr_block.block.clone();
            let mut stmts = prelude_block.stmts;
            stmts.append(&mut block.stmts);
            block.stmts = stmts;
            syn::Expr::Block(syn::ExprBlock {
                attrs: Vec::new(),
                label: None,
                block,
            })
        }
        ref orig_body => {
            let mut block = prelude_block;
            block.stmts.push(syn::Stmt::Expr(orig_body.clone(), None));
            syn::Expr::Block(syn::ExprBlock {
                attrs: Vec::new(),
                label: None,
                block,
            })
        }
    };
    closure.body = Box::new(new_body);

    Ok(closure)
}

/// Conjoins predicate expressions with `&&`, defaulting to `true` when empty.
fn conjoin(preds: &[TokenStream2]) -> TokenStream2 {
    if preds.is_empty() {
        return quote!(true);
    }
    let mut iter = preds.iter();
    let first = iter.next().unwrap();
    let mut acc = quote!((#first));
    for pred in iter {
        acc = quote!(#acc && (#pred));
    }
    acc
}
