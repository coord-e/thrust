//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// This is an alternative version of `annot_preds_impl.rs` without `impl` blocks.

// A is represented as Tuple<Int> in SMT-LIB2 format.
struct A {
    x: i64,
}

#[thrust::predicate]
fn is_double(a: &A, doubled: &A) -> bool {
    // (tuple_proj<Int>.0 a) is equivalent to a.x
    // a.x * 2 == doubled.x is written as following:
    "(=
        (* (tuple_proj<Int>.0 a) 2)
        (tuple_proj<Int>.0 doubled)
    )"; true
}

#[thrust::requires(true)]
#[thrust::ensures(is_double(*a, ^a))]
fn double(a: &mut A) {
    a.x += a.x;
}

fn main() {
    let mut a = A{x: 3};
    double(&mut a);
    assert!(a.x == 6);
}
