use std::collections::HashSet;

use proc_macro2::TokenStream as TokenStream2;
use quote::{quote, ToTokens as _};
use syn::visit::Visit as _;

use crate::fn_outer_item::FnOuterItem;

#[derive(Debug, Clone)]
pub struct FormulaFnTypeLowering<'a> {
    sig: &'a syn::Signature,
    outer_context: Option<&'a FnOuterItem>,
    closure_type_params: HashSet<syn::Ident>,
}

impl<'a> FormulaFnTypeLowering<'a> {
    pub fn new(sig: &'a syn::Signature) -> Self {
        let mut closure_type_params = Default::default();
        collect_closure_type_params(&sig.generics, &mut closure_type_params);
        Self {
            sig,
            outer_context: None,
            closure_type_params,
        }
    }

    pub fn with_outer_context(sig: &'a syn::Signature, outer_context: &'a FnOuterItem) -> Self {
        let mut closure_type_params = Default::default();
        collect_closure_type_params(&sig.generics, &mut closure_type_params);
        collect_closure_type_params(outer_context.generics(), &mut closure_type_params);
        Self {
            sig,
            outer_context: Some(outer_context),
            closure_type_params,
        }
    }

    /// Maps each function parameter `x: T` to `x: <T as thrust_models::Model>::Ty`.
    ///
    /// Parameters whose type is a closure/function type parameter `F` stay as `F`, so marker
    /// functions can recover the instantiated closure definition from the argument type.
    pub fn lower_params<'ast, I>(&self, args: I) -> TokenStream2
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
                    if self.is_closure_type_param(ty) {
                        model_inputs.push(syn::parse_quote!(#pat: #ty));
                    } else {
                        model_inputs
                            .push(syn::parse_quote!(#pat: <#ty as thrust_models::Model>::Ty));
                    }
                }
            }
        }
        quote!(#(#model_inputs),*)
    }

    pub fn lower_return_type(&self, ret: &syn::ReturnType) -> syn::Type {
        match ret {
            syn::ReturnType::Default => syn::parse_quote!(<() as thrust_models::Model>::Ty),
            syn::ReturnType::Type(_, ty) => {
                if self.is_closure_type_param(ty) {
                    *ty.clone()
                } else {
                    syn::parse_quote!(<#ty as thrust_models::Model>::Ty)
                }
            }
        }
    }

    pub fn model_where_predicates_for(&self, param: &syn::Ident) -> Vec<syn::WherePredicate> {
        if self.closure_type_params.contains(param) {
            Vec::new()
        } else {
            model_predicates(param).to_vec()
        }
    }

    /// `T: Model` / `<T as Model>::Ty: PartialEq` predicates for every type param
    /// in scope for `sig` (its own, plus the outer `impl`/`trait`'s and, for a
    /// trait, `Self`) that does not carry an `Fn`/`FnOnce`/`FnMut` bound, plus the
    /// same for any generic associated-type projection appearing in `sig` and for
    /// every associated type (`Self::Item`) declared by the outer `impl`/`trait`.
    pub fn model_where_predicates(&self) -> Vec<syn::WherePredicate> {
        let mut generic_type_params: Vec<syn::Ident> = Vec::new();
        for param in &self.sig.generics.params {
            let syn::GenericParam::Type(tp) = param else {
                continue;
            };
            generic_type_params.push(tp.ident.clone());
        }
        if let Some(outer_context) = &self.outer_context {
            for param in &outer_context.generics().params {
                let syn::GenericParam::Type(tp) = param else {
                    continue;
                };
                generic_type_params.push(tp.ident.clone());
            }
            if let FnOuterItem::ItemTrait(item_trait) = outer_context {
                if !has_fn_bound(item_trait.supertraits.iter()) {
                    generic_type_params.push(quote::format_ident!("Self"));
                }
            }
        }
        generic_type_params.retain(|p| !self.closure_type_params.contains(p));

        let mut predicates: Vec<syn::WherePredicate> = Vec::new();
        for param in &generic_type_params {
            predicates.extend(model_predicates(param));
        }

        struct Visitor {
            generic_type_params: Vec<syn::Ident>,
            generic_paths: Vec<syn::TypePath>,
        }

        impl syn::visit::Visit<'_> for Visitor {
            fn visit_type_path(&mut self, tp: &syn::TypePath) {
                for param in &self.generic_type_params {
                    if let Some(qself) = &tp.qself {
                        let param_ty: syn::Type = syn::parse_quote!(#param);
                        if *qself.ty == param_ty {
                            self.generic_paths.push(tp.clone());
                        }
                    }
                    if tp.path.segments.len() > 1
                        && &tp.path.segments.first().unwrap().ident == param
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
        for arg in &self.sig.inputs {
            visitor.visit_fn_arg(arg);
        }
        visitor.visit_return_type(&self.sig.output);
        for tp in visitor.generic_paths {
            predicates.extend(model_predicates(&tp));
        }

        if let Some(outer_context) = &self.outer_context {
            for assoc in outer_context.associated_type_idents() {
                let projection = quote!(Self::#assoc);
                predicates.extend(model_predicates(&projection));
            }
        }

        // Distinct predicates only: signature scanning and the associated-type
        // enumeration above can both yield the same `Self::Item` bound.
        let mut seen = HashSet::new();
        predicates.retain(|pred| seen.insert(pred.to_token_stream().to_string()));

        predicates
    }

    fn is_closure_type_param(&self, ty: &syn::Type) -> bool {
        let syn::Type::Path(tp) = ty else {
            return false;
        };
        if tp.qself.is_some() {
            return false;
        }
        let Some(ident) = tp.path.get_ident() else {
            return false;
        };
        self.closure_type_params.contains(ident)
    }
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

fn collect_closure_type_params(generics: &syn::Generics, result: &mut HashSet<syn::Ident>) {
    for param in &generics.params {
        let syn::GenericParam::Type(tp) = param else {
            continue;
        };
        if has_fn_bound(&tp.bounds) {
            result.insert(tp.ident.clone());
        }
    }
    if let Some(where_clause) = &generics.where_clause {
        for pred in &where_clause.predicates {
            let syn::WherePredicate::Type(pt) = pred else {
                continue;
            };
            let syn::Type::Path(tp) = &pt.bounded_ty else {
                continue;
            };
            if let Some(ident) = tp.path.get_ident() {
                if has_fn_bound(&pt.bounds) {
                    result.insert(ident.clone());
                }
            }
        }
    }
}

fn model_predicates(ty: &impl quote::ToTokens) -> [syn::WherePredicate; 2] {
    [
        syn::parse_quote!(#ty: thrust_models::Model),
        syn::parse_quote!(<#ty as thrust_models::Model>::Ty: PartialEq),
    ]
}
