//@check-pass
//@compile-flags: -Adead_code

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

    #[thrust_macros::predicate]
    fn can_double(self) -> bool {
        i64::MIN <= self.x + self.x && self.x + self.x <= i64::MAX
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
    #[thrust_macros::predicate]
    fn is_double(self, doubled: Self) -> bool {
        self.x * 2 == doubled.x && self.y * 2 == doubled.y
    }

    #[thrust_macros::predicate]
    fn can_double(self) -> bool {
        i64::MIN <= self.x + self.x && self.x + self.x <= i64::MAX
            && i64::MIN <= self.y + self.y && self.y + self.y <= i64::MAX
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
