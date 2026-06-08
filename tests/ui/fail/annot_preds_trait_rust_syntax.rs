//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A is represented as Tuple<Int> in SMT-LIB2 format.
#[derive(PartialEq)]
struct A {
    x: i64,
}

impl thrust_models::Model for A {
    type Ty = Self;
}

#[thrust_macros::context]
trait Double {
    // Support annotations in trait definitions
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool;

    // This annotations are applied to all implementors of the `Double` trait.
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::is_double(*self, !self))]
    fn double(&mut self);
}

#[thrust_macros::context]
impl Double for A {
    // self.x * 3 (this isn't actually doubled!) does not comply with the trait.
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.x * 3 == doubled.x
    }

    // Check if this method complies with annotations in
    // trait definition.
    fn double(&mut self) {
        self.x += self.x;
    }
}

fn main() {
    let mut a = A { x: 3 };
    a.double();
    assert!(a.x == 6);
}
