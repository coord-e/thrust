use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;

mod context;
mod fn_outer_item;
mod invariant;
mod invariant_context;
mod spec;

#[proc_macro_attribute]
pub fn context(_attr: TokenStream, item: TokenStream) -> TokenStream {
    context::expand(item)
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
///
/// Applied to a single function; a method recovers its enclosing
/// `impl`/`trait` context from `#[thrust_macros::context]` on the surrounding
/// block, as `requires`/`ensures` do.
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

/// Maps each function parameter `x: T` to `x: <T as thrust_models::Model>::Ty`.
fn fn_params_with_model_ty<'ast, I>(args: I) -> TokenStream2
where
    I: IntoIterator<Item = &'ast syn::FnArg>,
{
    let mut model_inputs: Vec<syn::FnArg> = Vec::new();
    for arg in args {
        match arg {
            syn::FnArg::Receiver(receiver) => {
                let ty = &receiver.ty;
                model_inputs.push(syn::parse_quote!(self_: <#ty as thrust_models::Model>::Ty));
            }
            syn::FnArg::Typed(pt) => {
                let pat = &pt.pat;
                let ty = &pt.ty;
                model_inputs.push(syn::parse_quote!(#pat: <#ty as thrust_models::Model>::Ty));
            }
        }
    }
    quote::quote!(#(#model_inputs),*)
}
