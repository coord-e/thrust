//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

use thrust_models::Model;

// A trait whose spec mentions an associated-type projection (`Self::Item`)
// only inside the formula body. The lowered predicate signatures must still
// carry the `Self::Item: Model` / `<Self::Item as Model>::Ty: PartialEq`
// bounds, which are derived from the trait's associated types rather than the
// method signature.

#[thrust_macros::context]
trait Source {
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, x: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::exists(|x: <Self::Item as Model>::Ty| Self::produces(*self, x)))]
    fn nonempty(&self) {}
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
