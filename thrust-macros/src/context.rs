//! Expansion of `#[thrust_macros::context]`.
//!
//! Stamps each method in an `impl`/`trait` block with the enclosing header so
//! method-level `requires`/`ensures` can recover the outer generics.

use proc_macro::TokenStream;
use quote::ToTokens as _;

use crate::fn_outer_item::FnOuterItem;

pub fn expand(item: TokenStream) -> TokenStream {
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
