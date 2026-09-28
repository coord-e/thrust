//@check-pass
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

    #[thrust_macros::predicate]
    fn can_double(self) -> bool;

    // This annotations are applied to all implementors of the `Double` trait.
    #[thrust_macros::requires(Self::can_double(*self))]
    #[thrust_macros::ensures(Self::is_double(*self, !self))]
    fn double(&mut self);
}

#[thrust_macros::context]
impl Double for A {
    #[thrust_macros::predicate]
    fn can_double(self) -> bool {
        -4611686018427387904_i64 <= self.x && self.x < 4611686018427387904_i64
    }

    // Write concrete definitions for predicates in `impl` blocks, in Rust syntax.
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.x * 2 == doubled.x
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
