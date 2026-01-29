//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

// A is represented as Tuple<Int> in SMT-LIB2 format.
struct A {
    x: i64,
}

trait Double {
    // Support annotations in trait definitions
    #[thrust::predicate]
    fn is_double(self, doubled: Self) -> bool;

    // This annotations are applied to all implementors of the `Double` trait.
    #[thrust::requires(true)]
    #[thrust::ensures(is_double(*self, ^self))]
    fn double(&mut self);
}

impl Double for A {
    // Write concrete definitions for predicates in `impl` blocks
    #[thrust::predicate]
    fn is_double(self, doubled: Self) -> bool {
        // (tuple_proj<Int>.0 self) is equivalent to self.x
        // self.x * 3 == doubled.x (this isn't actually doubled!) is written as following:
        "(=
            (* (tuple_proj<Int>.0 self) 3)
            (tuple_proj<Int>.0 doubled)
        )"; true // This definition does not comply with annotations in trait!
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
