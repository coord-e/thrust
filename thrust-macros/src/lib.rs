use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};

mod context;
mod fn_outer_item;
mod formula;
mod formula_fn_type_lowering;
mod invariant;
mod invariant_context;
mod pre_post;
mod rty;
mod spec;

use fn_outer_item::FnOuterItem;
use formula_fn_type_lowering::FormulaFnTypeLowering;

/// `pre!(f(a, b))` refers to the precondition of the closure `f` for arguments `a, b` in a
/// specification.
#[proc_macro]
pub fn pre(input: TokenStream) -> TokenStream {
    pre_post::expand_pre(input)
}

/// `post!(f(a, b), r)` refers to the postcondition of the closure `f` relating arguments
/// `a, b` to the result `r` in a specification.
#[proc_macro]
pub fn post(input: TokenStream) -> TokenStream {
    pre_post::expand_post(input)
}

#[proc_macro_attribute]
pub fn context(_attr: TokenStream, item: TokenStream) -> TokenStream {
    context::expand(item)
}

/// Preprocesses a formula body (see [`mod@formula`]); not written by hand.
#[proc_macro]
pub fn formula(input: TokenStream) -> TokenStream {
    formula::expand(input.into()).into()
}

/// Declares a loop invariant inside a loop body:
///
/// ```ignore
/// fn f() {
///     while cond {
///         thrust_macros::invariant!(|x: i64| x >= 1);
///         ...
///     }
/// }
/// ```
///
/// The argument is a closure whose parameters name the live variables the
/// invariant refers to (with their types) and whose body is the invariant
/// predicate.
#[proc_macro]
pub fn invariant(input: TokenStream) -> TokenStream {
    invariant::expand(input)
}

/// Context-carrying counterpart of `invariant!`, emitted by
/// `#[thrust_macros::invariant_context]`. Not intended to be written by hand:
/// it takes a `fn` header carrying the threaded generics/where clause whose
/// body is the predicate closure (see [`invariant`]).
#[proc_macro]
pub fn _invariant_with_context(input: TokenStream) -> TokenStream {
    invariant::expand_with_context(input)
}

/// Threads the surrounding generic context (and, in methods, `Self`) into
/// every `thrust_macros::invariant!(...)` inside the annotated function, so an
/// invariant may refer to generic- and `Self`-typed variables that the
/// standalone `invariant!` macro cannot see. Each such call is rewritten into
/// `thrust_macros::_invariant_with_context!`.
#[proc_macro_attribute]
pub fn invariant_context(_attr: TokenStream, item: TokenStream) -> TokenStream {
    invariant_context::expand(item)
}

#[proc_macro_attribute]
pub fn predicate(_attr: TokenStream, item: TokenStream) -> TokenStream {
    spec::expand_predicate(item)
}

#[proc_macro_attribute]
pub fn requires(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec::expand_requires(attr, item)
}

#[proc_macro_attribute]
pub fn ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec::expand_ensures(attr, item)
}

#[proc_macro_attribute]
pub fn _requires_ensures(attr: TokenStream, item: TokenStream) -> TokenStream {
    spec::expand_requires_ensures(attr, item)
}

/// Reads the `#[thrust::_outer_context(..)]` attribute stamped onto methods by
/// `#[thrust_macros::context]` (and threaded by `invariant_context`), returning
/// the enclosing `impl`/`trait` header it carries, or `None` if absent.
fn extract_outer_context(attrs: &[syn::Attribute]) -> syn::Result<Option<FnOuterItem>> {
    let outer_context_path: syn::Path = syn::parse_quote!(thrust::_outer_context);
    let mut outer_context = None;
    for attr in attrs {
        if attr.path() != &outer_context_path {
            continue;
        }
        if outer_context.is_some() {
            return Err(syn::Error::new_spanned(
                attr,
                "multiple _outer_context attributes found; expected at most one",
            ));
        }
        outer_context = Some(attr.parse_args()?);
    }
    Ok(outer_context)
}

#[proc_macro_attribute]
pub fn param(attr: TokenStream, item: TokenStream) -> TokenStream {
    rty::expand_param(attr, item)
}

#[proc_macro_attribute]
pub fn ret(attr: TokenStream, item: TokenStream) -> TokenStream {
    rty::expand_ret(attr, item)
}

#[proc_macro_attribute]
pub fn sig(attr: TokenStream, item: TokenStream) -> TokenStream {
    rty::expand_sig(attr, item)
}

fn tokens_contain_ident<T>(tokens: &TokenStream2, target: T) -> bool
where
    T: AsRef<str>,
{
    let target = target.as_ref();
    tokens.clone().into_iter().any(|tt| match tt {
        TokenTree2::Ident(ident) => ident == target,
        TokenTree2::Group(group) => tokens_contain_ident(&group.stream(), target),
        _ => false,
    })
}
