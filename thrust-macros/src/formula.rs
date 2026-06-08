//! The `thrust_macros::formula!` proc-macro: the single preprocessing layer for
//! formula tokens.
//!
//! Annotation macros wrap their formula body in `thrust_macros::formula!(...)`
//! instead of splicing it raw. This hides syntax that is not valid Rust (the
//! `==>` operator) inside a macro call's arguments, so the surrounding pipeline —
//! which parses formulas as [`syn::Expr`] — never chokes on it, and gives one
//! place to run preprocessing before the body reaches rustc / HIR lowering.
//!
//! The only pass today is implication desugaring; further passes can be appended
//! in [`expand`].

use proc_macro2::{Group, Punct, Spacing, TokenStream, TokenTree};
use quote::{quote, ToTokens};
use syn::visit_mut::VisitMut;

/// Wraps formula tokens in a `thrust_macros::formula!(...)` call.
pub fn wrap_expr(tokens: TokenStream) -> TokenStream {
    quote!(::thrust_macros::formula!(#tokens))
}

/// Wraps an invariant closure's body in `::thrust_macros::formula!(...)`, taking
/// everything past the closure header (the first two top-level `|`) as the body.
/// Only the body is wrapped: the closure must stay a parseable `ExprClosure` for
/// `invariant::expand_invariant` to read its `.inputs`/`.body`, and the context
/// form's threaded signature must not be preprocessed. Non-closure inputs pass
/// through.
///
/// A closure with an explicit return type (`|x| -> Ty { .. }`) must keep its body
/// a block, so the `-> Ty {` / `}` is preserved and only the block's tail
/// expression is wrapped.
pub fn wrap_closure_body(input: TokenStream) -> TokenStream {
    let tokens: Vec<TokenTree> = input.into_iter().collect();
    let bars: Vec<usize> = tokens
        .iter()
        .enumerate()
        .filter(|(_, tt)| matches!(tt, TokenTree::Punct(p) if p.as_char() == '|'))
        .map(|(i, _)| i)
        .collect();
    let [_open, close, ..] = bars[..] else {
        return tokens.into_iter().collect();
    };
    let header: TokenStream = tokens[..=close].iter().cloned().collect();
    let tail = &tokens[close + 1..];

    // `-> Ty { body }`: wrap the block's tail expression in place.
    let has_return_type = matches!(tail.first(), Some(TokenTree::Punct(p)) if p.as_char() == '-')
        && matches!(tail.get(1), Some(TokenTree::Punct(p)) if p.as_char() == '>');
    if has_return_type {
        if let Some((TokenTree::Group(block), prefix)) = tail.split_last() {
            if block.delimiter() == proc_macro2::Delimiter::Brace {
                let prefix: TokenStream = prefix.iter().cloned().collect();
                let body = wrap_block_tail(block);
                return quote!(#header #prefix #body);
            }
        }
    }

    // `|args| body`: the body is a bare expression; wrap it whole.
    let body = wrap_expr(tail.iter().cloned().collect());
    quote!(#header #body)
}

/// Returns a brace group like `block` but with its tail expression (the final
/// `;`-separated segment) wrapped in `::thrust_macros::formula!(...)`. Leading
/// statements are left untouched; a block with no tail expression is unchanged.
fn wrap_block_tail(block: &Group) -> TokenStream {
    let stmts: Vec<TokenTree> = block.stream().into_iter().collect();
    let mut segments: Vec<Vec<TokenTree>> = vec![Vec::new()];
    for tt in &stmts {
        segments.last_mut().unwrap().push(tt.clone());
        if matches!(tt, TokenTree::Punct(p) if p.as_char() == ';') {
            segments.push(Vec::new());
        }
    }
    let tail = segments.pop().unwrap();

    let mut inner = TokenStream::new();
    for seg in &segments {
        inner.extend(seg.iter().cloned());
    }
    if !tail.is_empty() {
        inner.extend(wrap_expr(tail.into_iter().collect()));
    }

    let mut wrapped = Group::new(proc_macro2::Delimiter::Brace, inner);
    wrapped.set_span(block.span());
    quote!(#wrapped)
}

/// Expands `formula!(<tokens>)` into the preprocessed boolean expression.
pub fn expand(input: TokenStream) -> TokenStream {
    if let Err(e) = reject_bare_assignment(&input) {
        return e.to_compile_error();
    }

    // `==>` is desugared to assignment (the lowest-precedence, right-associative
    // operator) so `syn` reproduces its precedence, then each assignment node is
    // rewritten into `!lhs || rhs`.
    let desugared = desugar_arrows(input);
    let mut expr: syn::Expr = match syn::parse2(desugared) {
        Ok(expr) => expr,
        Err(e) => return e.to_compile_error(),
    };

    // Rewrites each assignment `lhs = rhs` (produced by [`desugar_arrows`] from
    // `lhs ==> rhs`) into `(!(lhs)) || (rhs)`. Visiting post-order means nested
    // implications are rewritten innermost-first, so the right-associative chain
    // `a ==> b ==> c` becomes `!a || (!b || c)`.
    struct ImplicationRewriter;

    impl VisitMut for ImplicationRewriter {
        fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
            syn::visit_mut::visit_expr_mut(self, expr);
            if let syn::Expr::Assign(assign) = expr {
                let left = &assign.left;
                let right = &assign.right;
                *expr = syn::parse_quote!((!(#left)) || (#right));
            }
        }
    }

    ImplicationRewriter.visit_expr_mut(&mut expr);

    expr.into_token_stream()
}

/// Rejects a bare assignment `=` anywhere in `input`. Desugaring turns `==>` into
/// `=`, so a genuine `=` would be read as an implication; since assignment is
/// meaningless in a formula we reject it up front. A genuine `=` is a lone
/// `Punct('=')` with [`Spacing::Alone`] not preceded by a joint punct, which
/// excludes the `=`s of `==`, `!=`, `<=`, `>=`, and `==>`.
fn reject_bare_assignment(input: &TokenStream) -> syn::Result<()> {
    let mut prev_joint = false;
    for tt in input.clone() {
        match tt {
            TokenTree::Group(g) => {
                reject_bare_assignment(&g.stream())?;
                prev_joint = false;
            }
            TokenTree::Punct(p) => {
                if p.as_char() == '=' && p.spacing() == Spacing::Alone && !prev_joint {
                    return Err(syn::Error::new(
                        p.span(),
                        "`=` is not allowed in a formula; use `==` for equality or `==>` for implication",
                    ));
                }
                prev_joint = p.spacing() == Spacing::Joint;
            }
            _ => prev_joint = false,
        }
    }
    Ok(())
}

/// Replaces every contiguous `==>` (the puncts `=`, `=`, `>`) with a single `=`,
/// recursing into every delimiter group. `==`, `=>`, `>=`, and `->` do not match
/// the triple and are left untouched.
fn desugar_arrows(input: TokenStream) -> TokenStream {
    let mut out = TokenStream::new();
    let mut iter = input.into_iter().peekable();
    while let Some(tt) = iter.next() {
        match tt {
            TokenTree::Group(group) => {
                let inner = desugar_arrows(group.stream());
                let mut new_group = Group::new(group.delimiter(), inner);
                new_group.set_span(group.span());
                out.extend([TokenTree::Group(new_group)]);
            }
            TokenTree::Punct(p) if p.as_char() == '=' && p.spacing() == Spacing::Joint => {
                // Look for a contiguous `==>`: `p` is the first `=`, joint to a
                // second joint `=`, then a `>`. Requiring joint spacing avoids
                // matching a spaced-out `= = >` / `== >`.
                if let Some(TokenTree::Punct(p2)) = iter.peek() {
                    if p2.as_char() == '=' && p2.spacing() == Spacing::Joint {
                        let mut lookahead = iter.clone();
                        lookahead.next(); // consume the second `=`
                        if let Some(TokenTree::Punct(p3)) = lookahead.peek() {
                            if p3.as_char() == '>' {
                                // Matched `==>`; consume `=` and `>`, emit `=`.
                                iter.next(); // second `=`
                                iter.next(); // `>`
                                let mut eq = Punct::new('=', Spacing::Alone);
                                eq.set_span(p.span());
                                out.extend([TokenTree::Punct(eq)]);
                                continue;
                            }
                        }
                    }
                }
                out.extend([TokenTree::Punct(p)]);
            }
            other => out.extend([other]),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `expand`s `s`, then renders it through `syn` so spacing matches `expect`.
    fn expand_expr(s: &str) -> String {
        let expr: syn::Expr = syn::parse2(expand(s.parse().unwrap())).unwrap();
        quote!(#expr).to_string()
    }

    fn expect(s: &str) -> String {
        let expr: syn::Expr = syn::parse_str(s).unwrap();
        quote!(#expr).to_string()
    }

    #[test]
    fn desugars_implication() {
        assert_eq!(expand_expr("a ==> b"), expect("(!(a)) || (b)"));
        // right-associative
        assert_eq!(
            expand_expr("a ==> b ==> c"),
            expect("(!(a)) || ((!(b)) || (c))")
        );
        // lower precedence than `||` and `==`
        assert_eq!(
            expand_expr("a || b ==> c == d"),
            expect("(!(a || b)) || (c == d)")
        );
        // nested inside a closure argument
        assert_eq!(
            expand_expr("exists(|x| a ==> b)"),
            expect("exists(|x| (!(a)) || (b))")
        );
    }

    #[test]
    fn leaves_comparisons_untouched() {
        for s in ["a == b", "a != b", "a >= b", "a <= b"] {
            assert_eq!(expand_expr(s), expect(s), "{s}");
        }
    }

    #[test]
    fn rejects_bare_assignment() {
        // `expand` emits a `compile_error!` instead of a valid expression.
        for s in ["a = b", "f(x = y)"] {
            assert!(
                expand(s.parse().unwrap())
                    .to_string()
                    .contains("compile_error"),
                "{s}"
            );
        }
    }

    /// `wrap_closure_body` must leave the input a parseable `ExprClosure`, both
    /// for a bare-expression body and one with an explicit return type.
    fn assert_wraps_to_closure(s: &str) {
        let wrapped = wrap_closure_body(s.parse().unwrap());
        syn::parse2::<syn::ExprClosure>(wrapped).unwrap_or_else(|e| panic!("{s}: {e}"));
    }

    #[test]
    fn preserves_closure_forms() {
        assert_wraps_to_closure("|x: i64| x >= 1 ==> x >= 0");
        assert_wraps_to_closure("|x: i64| -> bool { x >= 1 ==> x >= 0 }");
    }
}
