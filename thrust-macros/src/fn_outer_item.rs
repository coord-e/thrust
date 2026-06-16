/// An `impl` or `trait` header carried by the `#[thrust::_outer_context(..)]`
/// attribute so a method can recover its enclosing generics.
#[derive(Debug, Clone)]
pub enum FnOuterItem {
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
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        match self {
            FnOuterItem::ItemImpl(item_impl) => item_impl.to_tokens(tokens),
            FnOuterItem::ItemTrait(item_trait) => item_trait.to_tokens(tokens),
        }
    }
}

impl FnOuterItem {
    /// Strips method (and other) items but keeps associated `type` declarations
    pub fn into_header_only(mut self) -> Self {
        match &mut self {
            FnOuterItem::ItemImpl(item_impl) => {
                item_impl
                    .items
                    .retain(|item| matches!(item, syn::ImplItem::Type(_)));
            }
            FnOuterItem::ItemTrait(item_trait) => {
                item_trait
                    .items
                    .retain(|item| matches!(item, syn::TraitItem::Type(_)));
            }
        }
        self
    }

    pub fn generics(&self) -> &syn::Generics {
        match self {
            FnOuterItem::ItemImpl(item_impl) => &item_impl.generics,
            FnOuterItem::ItemTrait(item_trait) => &item_trait.generics,
        }
    }

    /// The names of the associated types declared in this `impl`/`trait` header.
    pub fn associated_type_idents(&self) -> Vec<syn::Ident> {
        // TODO: handle generic associated types. We only emit bounds for a bare
        // `Self::Assoc` projection, so a GAT (`type Item<U>;`) is skipped to avoid
        // fabricating an ill-formed `Self::Item: Model` bound (E0107).
        match self {
            FnOuterItem::ItemImpl(item_impl) => item_impl
                .items
                .iter()
                .filter_map(|item| match item {
                    syn::ImplItem::Type(ty) if ty.generics.params.is_empty() => {
                        Some(ty.ident.clone())
                    }
                    _ => None,
                })
                .collect(),
            FnOuterItem::ItemTrait(item_trait) => item_trait
                .items
                .iter()
                .filter_map(|item| match item {
                    syn::TraitItem::Type(ty) if ty.generics.params.is_empty() => {
                        Some(ty.ident.clone())
                    }
                    _ => None,
                })
                .collect(),
        }
    }
}
