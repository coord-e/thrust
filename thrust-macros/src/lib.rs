use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, TokenTree as TokenTree2};

mod context;
mod fn_outer_item;
mod invariant;
mod invariant_context;
mod spec;

use fn_outer_item::FnOuterItem;

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

fn has_fn_bound<'a>(bounds: impl IntoIterator<Item = &'a syn::TypeParamBound>) -> bool {
    bounds.into_iter().any(|b| {
        let syn::TypeParamBound::Trait(tb) = b else {
            return false;
        };
        tb.path
            .segments
            .last()
            .is_some_and(|s| matches!(s.ident.to_string().as_str(), "Fn" | "FnOnce" | "FnMut"))
    })
}

fn model_predicates(ty: &impl quote::ToTokens) -> [syn::WherePredicate; 2] {
    [
        syn::parse_quote!(#ty: thrust_models::Model),
        syn::parse_quote!(<#ty as thrust_models::Model>::Ty: PartialEq),
    ]
}

/// `T: Model` / `<T as Model>::Ty: PartialEq` predicates for every type param
/// in scope for `sig` (its own, plus the outer `impl`/`trait`'s and, for a
/// trait, `Self`) that does not carry an `Fn`/`FnOnce`/`FnMut` bound, plus the
/// same for any generic associated-type projection appearing in `sig`.
fn model_where_predicates(
    sig: &syn::Signature,
    outer_context: Option<&FnOuterItem>,
) -> Vec<syn::WherePredicate> {
    struct GenericTypeParam {
        ident: syn::Ident,
        bounds: Vec<syn::TypeParamBound>,
    }

    impl From<syn::TypeParam> for GenericTypeParam {
        fn from(tp: syn::TypeParam) -> Self {
            Self {
                ident: tp.ident,
                bounds: tp.bounds.into_iter().collect(),
            }
        }
    }

    let mut generic_type_params: Vec<GenericTypeParam> = Vec::new();
    for param in &sig.generics.params {
        let syn::GenericParam::Type(tp) = param else {
            continue;
        };
        generic_type_params.push(tp.clone().into());
    }
    if let Some(outer_item) = outer_context {
        for param in &outer_item.generics().params {
            let syn::GenericParam::Type(tp) = param else {
                continue;
            };
            generic_type_params.push(tp.clone().into());
        }
        if let FnOuterItem::ItemTrait(outer_item) = &outer_item {
            generic_type_params.push(GenericTypeParam {
                ident: quote::format_ident!("Self"),
                bounds: outer_item.supertraits.iter().cloned().collect(),
            });
        }
    }
    generic_type_params.retain(|p| !has_fn_bound(&p.bounds));

    let mut predicates: Vec<syn::WherePredicate> = Vec::new();
    for param in &generic_type_params {
        predicates.extend(model_predicates(&param.ident));
    }

    struct Visitor {
        generic_type_params: Vec<GenericTypeParam>,
        generic_paths: Vec<syn::TypePath>,
    }

    impl syn::visit::Visit<'_> for Visitor {
        fn visit_type_path(&mut self, tp: &syn::TypePath) {
            for param in &self.generic_type_params {
                if let Some(qself) = &tp.qself {
                    let param = &param.ident;
                    let param_ty: syn::Type = syn::parse_quote!(#param);
                    if *qself.ty == param_ty {
                        self.generic_paths.push(tp.clone());
                    }
                }
                if tp.path.segments.len() > 1
                    && tp.path.segments.first().unwrap().ident == param.ident
                    && tp.qself.is_none()
                {
                    self.generic_paths.push(tp.clone());
                }
            }
            syn::visit::visit_type_path(self, tp);
        }
    }

    let mut visitor = Visitor {
        generic_type_params,
        generic_paths: Vec::new(),
    };
    use syn::visit::Visit as _;
    for arg in &sig.inputs {
        visitor.visit_fn_arg(arg);
    }
    visitor.visit_return_type(&sig.output);
    for tp in visitor.generic_paths {
        predicates.extend(model_predicates(&tp));
    }

    predicates
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
