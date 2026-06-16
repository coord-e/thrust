//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

// The associated-type projection `Self::Item` appears only inside the `ensures` expression (not in
// the method signature), so the macro must emit its `Model`/`PartialEq` bounds for the lowered
// `exists` binder and predicate call to type-check. `produces` holds for every item, so a produced
// item exists ("the source is non-empty").

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
        "true";
        true
    }
}

fn main() {
    let s = S { v: 1 };
    s.nonempty();
}
