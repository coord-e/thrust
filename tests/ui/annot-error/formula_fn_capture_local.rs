// Reproduces: a `formula_fn` produced by `requires`/`ensures`/`invariant!`
// cannot capture the surrounding function's local bindings (E0434 "can't
// capture dynamic environment in a fn item").
//
// The macro lowers the spec into a free `fn _thrust_ensures_X(...)` whose
// only inputs are the host parameters (lowered to their `Model::Ty`) and
// the closure's bound variables. Any reference to a `let`-bound name in
// the host function is rejected.
//
// Same shape, applied to `_invariant_with_context!`: the host signature
// re-declared in the macro head (e.g. `fn run<B, F>(self, f: B, g: F)`)
// is *not* threaded into the `formula_fn` parameters either; the macro
// currently only lowers the closure params plus the synthetic
// `__ThrustSelf` (for `Self` rewrite).
//
// No annotation-side workaround: this is a macro bug in
// `thrust-macros/src/invariant.rs::expand_invariant` (the host-signature
// re-declaration is parsed but its parameters are dropped on the floor).
// Either fix the macro to lower the re-declared signature's params via
// `type_lowering.lower_params(...)` and add them to the formula_fn, or
// restructure the invariant to not mention the host parameters (which
// often defeats the point of the invariant).

#[thrust_macros::context]
trait Foo {
    fn run<B, F>(self, f: B, g: F) -> B
    where
        Self: Sized,
        F: FnOnce(B) -> B,
    {
        let mut x: i64 = 0;
        while x < 1 {
            thrust_macros::_invariant_with_context!(
                #[thrust::_outer_context(trait Foo {})]
                fn run<B, F>(self: Self, f: B, g: F) -> B
                where
                    Self: Sized,
                    F: FnOnce(B) -> B;
                |x: i64| x == f && g == f
            );
            x += 1;
        }
        f
    }
}

fn main() {}
