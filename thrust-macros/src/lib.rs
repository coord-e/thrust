use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};

mod closure;
mod context;
mod fn_outer_item;
mod formula;
mod formula_fn_lifting;
mod formula_fn_type_lowering;
mod ghost;
mod invariant;
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

/// `closure!(requires(..), ensures(..), |x: T| -> R { .. })` attaches an
/// explicit pre-/post-condition to a closure expression. Each clause is optional
/// (omitting one leaves that side inferred) and may be repeated (conjoined).
/// See [`mod@closure`].
#[proc_macro]
pub fn closure(input: TokenStream) -> TokenStream {
    closure::expand(input)
}

/// Introduces a ghost value: proof-only data with no runtime representation.
///
/// ```ignore
/// let s = thrust_macros::ghost!(|s: Ghost<Seq<Int>>, x: i64| -> Seq<Int> { s.push(x) });
/// ```
///
/// The argument is a closure whose parameters name the live variables the ghost term
/// refers to (with their types) and whose return type is the logical type of the value.
/// See [`mod@ghost`].
#[proc_macro]
pub fn ghost(input: TokenStream) -> TokenStream {
    ghost::expand(input)
}

/// Context-carrying counterpart of `ghost!`, emitted by
/// `#[thrust_macros::context]`. Not intended to be written by hand:
/// it takes a `fn` header carrying the threaded generics/where clause whose
/// body is the ghost term closure (see [`ghost`]).
#[proc_macro]
pub fn _ghost_with_context(input: TokenStream) -> TokenStream {
    ghost::expand_with_context(input)
}

/// Makes the enclosing context available to the specifications written inside an
/// item. On an `impl`/`trait`, each method recovers the outer generics (and `Self`)
/// in its `requires`/`ensures`; on a function — including a method reached that way —
/// every `thrust_macros::invariant!(...)` and `thrust_macros::ghost!(...)` in the body
/// may refer to generic- and `Self`-typed variables that the standalone macros cannot
/// see. See [`mod@context`].
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
/// `#[thrust_macros::context]`. Not intended to be written by hand:
/// it takes a `fn` header carrying the threaded generics/where clause whose
/// body is the predicate closure (see [`invariant`]).
#[proc_macro]
pub fn _invariant_with_context(input: TokenStream) -> TokenStream {
    invariant::expand_with_context(input)
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
/// `#[thrust_macros::context]` (and threaded into the formulas in their bodies),
/// returning the enclosing `impl`/`trait` header it carries, or `None` if absent.
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

/// Reconstructs the effective type of a method receiver (`&self` -> `&Self`,
/// `&mut self` -> `&mut Self`, `self` -> `Self`, `self: T` -> `T`), mirroring
/// what syn 2's `Receiver::ty` used to provide directly.
fn receiver_type(receiver: &syn::Receiver) -> syn::Type {
    match &receiver.kind {
        syn::ReceiverKind::Typed(_, ty) => (**ty).clone(),
        syn::ReceiverKind::Reference(and_token, lifetime, mutability) => {
            syn::Type::Reference(syn::TypeReference {
                attrs: Vec::new(),
                and_token: *and_token,
                lifetime: lifetime.clone(),
                mutability: *mutability,
                elem: Box::new(syn::parse_quote!(Self)),
            })
        }
        syn::ReceiverKind::Value => syn::parse_quote!(Self),
        _ => unimplemented!("unknown syn::ReceiverKind variant"),
    }
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
