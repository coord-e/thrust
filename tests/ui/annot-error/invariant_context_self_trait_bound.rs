// Reproduces: when an `_invariant_with_context!` rewrites `Self` to a
// synthetic `__ThrustSelf` generic in the injected `formula_fn`, it does
// NOT automatically propagate the host trait bound (here `Self: Foo`).
// Calling trait items (the user-defined predicates `completed` / `step`
// and the associated `Item` type) on the synthetic `Self` therefore
// fails with E0599 / E0220 "no function / associated type named X found
// for `__ThrustSelf`".
//
// See `invariant_context_self_trait_bound_workaround.rs` for a partial
// workaround (`Self: Sized + Foo` in the re-declared where clause) that
// silences E0599 (the trait method calls) but leaves E0220 (the
// associated type) untouched — fully fixing the latter requires the
// `expand_invariant` macro to also rewrite `Self` to `__ThrustSelf` in
// the propagated where-clause predicates.

#[thrust_macros::context]
trait Foo {
    type Item;

    #[thrust_macros::predicate]
    fn completed(self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;

    fn run<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while true {
            thrust_macros::_invariant_with_context!(
                #[thrust::_outer_context(trait Foo { type Item; })]
                fn run<B, F>(mut self: Self, init: B, mut f: F) -> B
                where
                    Self: Sized,
                    F: FnMut(B, Self::Item) -> B;
                |accum: B| thrust_models::exists(
                    |item: Self::Item|
                        Self::step(*self, item, *self)
                        && accum == init
                )
            );
            break;
        }
        accum
    }
}

fn main() {}
