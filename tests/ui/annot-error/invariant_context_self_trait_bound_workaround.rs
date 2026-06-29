// Annotation-side partial workaround for
// `invariant_context_self_trait_bound.rs`.
//
// Adding the host trait bound to the re-declared signature's where
// clause (`Self: Sized + Foo` instead of just `Self: Sized`) makes the
// `expand_invariant` macro copy it into the `formula_fn`'s where
// clause, so `__ThrustSelf: Foo` is in scope. That silences the trait
// method-call errors (E0599 for `__ThrustSelf::step` /
// `__ThrustSelf::completed`).
//
// What it does NOT fix: E0220 for `__ThrustSelf::Item`. The macro's
// `where_predicates()` walk copies the re-declared where-clause
// predicates verbatim — `Self` is *not* rewritten to `__ThrustSelf` in
// the copied predicates, so the copy still talks about `Self` (host
// type) rather than `__ThrustSelf` (synthetic). The associated type
// `Item` lookup goes through `Self` instead of `__ThrustSelf`, and Rust
// complains. Fully fixing this needs the macro to rewrite `Self` to
// `__ThrustSelf` in the propagated where-clause predicates, then add
// `<__ThrustSelf as Foo>::Item` (or an analogous `Item` projection) to
// the `__ThrustSelf` parameter scope.

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
                    // ← the partial-fix: add the host trait bound to
                    //   the re-declared where clause. The macro copies
                    //   it to the formula_fn where, so __ThrustSelf: Foo
                    //   resolves the trait method calls.
                    Self: Sized + Foo,
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
