use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{FnArg, Generics};

mod context;
mod invariant;
mod spec;

// ===== proc-macro entry points =====
//
// A proc-macro crate must declare these at the crate root; each delegates to
// the relevant module.

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

// ===== shared helpers =====
//
// Used by more than one of the modules above. They live in the crate root and
// stay private: a private root item is visible to every descendant module, so
// no `pub(crate)` is required.

/// An `impl` or `trait` header carried by the `#[thrust::_outer_context(..)]`
/// attribute so a method can recover its enclosing generics.
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
