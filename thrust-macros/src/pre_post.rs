use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use syn::punctuated::Punctuated;

/// Builds a tuple expression from a call's argument list, for the closure precondition/postcondition
/// marker functions in `thrust_models::model`. An empty list becomes `()`; otherwise a trailing
/// comma makes a single argument a one-element tuple (`(x,)`).
fn call_args_tuple(args: &Punctuated<syn::Expr, syn::Token![,]>) -> TokenStream2 {
    if args.is_empty() {
        quote::quote!(())
    } else {
        let args = args.iter();
        quote::quote!((#(#args),*,))
    }
}

pub fn expand_pre(input: TokenStream) -> TokenStream {
    let call = syn::parse_macro_input!(input as syn::ExprCall);
    let func = &*call.func;
    let args = call_args_tuple(&call.args);
    quote::quote!(thrust_models::model::closure_precondition(#func, #args)).into()
}

pub fn expand_post(input: TokenStream) -> TokenStream {
    let parser = Punctuated::<syn::Expr, syn::Token![,]>::parse_terminated;
    let exprs = syn::parse_macro_input!(input with parser);
    let exprs: Vec<syn::Expr> = exprs.into_iter().collect();
    let [call_expr, result] = exprs.as_slice() else {
        return syn::Error::new(
            proc_macro2::Span::call_site(),
            "post! expects `post!(f(args), result)`",
        )
        .to_compile_error()
        .into();
    };
    let syn::Expr::Call(call) = call_expr else {
        return syn::Error::new_spanned(
            call_expr,
            "post! expects a call expression as its first argument, e.g. `post!(f(x), r)`",
        )
        .to_compile_error()
        .into();
    };
    let func = &*call.func;
    let args = call_args_tuple(&call.args);
    quote::quote!(thrust_models::model::closure_postcondition(#func, #args, #result)).into()
}
