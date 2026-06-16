//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// Same shape as the pass counterpart (the spec still uses the `Self::Item` projection), but
// `produces` holds for no item, so no produced item exists and the postcondition fails with
// `Unsat`.

#[thrust_macros::context]
trait Source {
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, x: Self::Item) -> bool;

    #[thrust_macros::ensures(
        thrust_models::exists(|x: <Self::Item as thrust_models::Model>::Ty| Self::produces(*self, x))
    )]
    fn nonempty(&self)
    where
        Self: Sized,
    {
    }
}

#[derive(PartialEq)]
struct S {
    v: i64,
}

impl thrust_models::Model for S {
    type Ty = S;
}

#[thrust_macros::context]
impl Source for S {
    type Item = i64;

    #[thrust_macros::predicate]
    fn produces(self, x: Self::Item) -> bool {
        "false";
        false
    }
}

fn main() {
    let s = S { v: 1 };
    s.nonempty();
}
