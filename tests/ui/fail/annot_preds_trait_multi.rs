//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

trait Double {
    // Support annotations in trait definitions
    #[thrust::predicate]
    fn is_double(self, doubled: Self) -> bool;

    // This annotations are applied to all implementors of the `Double` trait.
    #[thrust::requires(true)]
    #[thrust::ensures(Self::is_double(*self, ^self))]
    fn double(&mut self);
}

// A is represented as Tuple<Int> in SMT-LIB2 format.
struct A {
    x: i64,
}

impl Double for A {
    #[thrust::predicate]
    fn is_double(self, doubled: Self) -> bool {
        // self.x * 2 == doubled.x
        "(=
            (* (tuple_proj<Int>.0 self) 2)
            (tuple_proj<Int>.0 doubled)
        )"; true
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

impl Double for B {
    #[thrust::predicate]
    fn is_double(self, doubled: Self) -> bool {
        // self.x * 3 == doubled.x && self.y * 2 == doubled.y (this isn't actually doubled!)
        "(and
            (=
                (* (tuple_proj<Int-Int>.0 self) 3)
                (tuple_proj<Int-Int>.0 doubled)
            )
            (=
                (* (tuple_proj<Int-Int>.1 self) 2)
                (tuple_proj<Int-Int>.1 doubled)
            )
        )"; true // This definition does not comply with annotations in trait!
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
