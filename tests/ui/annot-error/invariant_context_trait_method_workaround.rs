// Annotation-side workaround for `invariant_context_trait_method.rs`.
//
// The `#[thrust_macros::invariant_context]` attribute is `ItemFn`-only
// (its `expand` parses as `syn::ItemFn`), so attaching it to a trait
// method triggers E0401 because the trait's `Self` is out of scope for
// the generated `formula_fn`. The other annotation-side attempt —
// hand-rolling `thrust_macros::_invariant_with_context!` inside the
// loop body — runs into the same problem (the macro's `SelfRewriter`
// only kicks in when the closure body actually mentions `Self`;
// otherwise `Self: Model` constraints are produced against the outer
// `Self` and Rust rejects them).
//
// Workaround: drop the invariant on the trait method, and instead
// provide it on the concrete impl method, where `invariant_context`
// works (`ItemFn` parse target). The impl is the only place the
// invariant is meaningful anyway: the trait method's spec is
// independent of any concrete iterator type.

#[thrust_macros::context]
trait Foo {
    type Item;

    fn run(&mut self);
}

struct Bar;

impl thrust_models::Model for Bar {
    type Ty = Bar;
}

#[thrust_macros::context]
impl Foo for Bar {
    type Item = i64;

    // `invariant_context` on an impl method is fine: the host is an
    // `ItemFn` (`impl` method) and `Self` is the impl's self-type,
    // not the trait's.
    #[thrust_macros::invariant_context]
    fn run(&mut self) {
        let mut x: i64 = 0;
        while x < 1 {
            thrust_macros::invariant!(|x: i64| x >= 0);
            x += 1;
        }
    }
}

fn main() {}
