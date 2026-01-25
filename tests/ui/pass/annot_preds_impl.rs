//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// A is represented as Tuple<Int> in SMT-LIB2 format.
struct A {
    x: i64,
}

impl A {
    // Support annotations for metheds in impl blocks

    #[thrust::predicate]
    fn is_double(&self, doubled: &Self) -> bool {
        // (tuple_proj<Int>.0 self) is equivalent to self.x
        // self.x * 2 == doubled.x is written as following:
        "(=
            (* (tuple_proj<Int>.0 self) 2)
            (tuple_proj<Int>.0 doubled)
        )"; true
    }

    #[thrust::requires(true)]
    #[thrust::ensures(*self.is_double(^self))]
    fn double(&mut self) {
        self.x += self.x;
    }
}

fn main() {
    let mut a = A { x: 3 };
    a.double();
    assert!(a.x == 6);
}
