// Reproduces: `#[thrust_macros::invariant_context]` attached to a *trait*
// method fails with E0401 ("can't use `Self` from outer item").
//
// `invariant_context` is `ItemFn`-only (`thrust-macros/src/invariant_context.rs`).
// On a trait method it parses, but it never threads the trait-level `Self`
// through to the generated `formula_fn`, so the injected
// `_invariant_with_context!` macro ends up rewriting the closure body against
// the outer trait's `Self` (which is out of scope) and Rust rejects the use.

#[thrust_macros::context]
trait Foo {
    type Item;

    #[thrust_macros::invariant_context]
    fn run(&mut self)
    where
        Self: Sized,
    {
        let mut x: i64 = 0;
        while x < 1 {
            thrust_macros::invariant!(|x: i64| x >= 0);
            x += 1;
        }
    }
}

fn main() {}
