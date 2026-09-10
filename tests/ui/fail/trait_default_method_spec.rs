//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// A default method's postcondition is checked once against the abstract predicate, so it
// has to hold for every implementor: `produces` is non-empty in the only impl here, but
// nothing in the trait says so, and the empty default body cannot establish it.

#[thrust_macros::context]
trait Source {
    type Item;

    #[thrust_macros::predicate]
    fn produces(self, x: Self::Item) -> bool;

    #[thrust_macros::ensures(thrust_models::exists(|x| Self::produces(*self, x)))]
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
        // x == self.v
        "(= x (tuple_proj<Int>.0 self_))";
        true
    }
}

fn main() {
    let s = S { v: 1 };
    s.nonempty();
}
