//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

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

// A is represented as Tuple<Int> in SMT-LIB2 format.
struct A {
    x: i64,
}

impl thrust_models::Model for A {
    type Ty = Self;
}

#[thrust_macros::context]
impl Double for A {
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.x * 2 == doubled.x
    }

    fn double(&mut self) {
        self.x += self.x;
    }
}

// B is represented as Tuple<Int, Int> in SMT-LIB2 format.
struct B {
    x: i64,
    y: i64,
}

impl thrust_models::Model for B {
    type Ty = Self;
}

#[thrust_macros::context]
impl Double for B {
    // self.x * 3 (this isn't actually doubled!) does not comply with the trait.
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.x * 3 == doubled.x && self.y * 2 == doubled.y
    }

    fn double(&mut self) {
        self.x += self.x;
        self.y += self.y;
    }
}

fn main() {
    let mut a = A { x: 3 };
    a.double();
    assert!(a.x == 6);

    let mut b = B { x: 2, y: 5 };
    b.double();
    assert!(b.x == 4 && b.y == 10);
}
