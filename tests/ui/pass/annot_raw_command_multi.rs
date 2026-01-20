//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

// Insert commands written in SMT-LIB2 format into .smt2 file directly.
// This feature is intended for debug or experiment purpose.
#![feature(custom_inner_attributes)]
#![thrust::raw_command("(define-fun is_double ((x Int) (doubled_x Int)) Bool
    (=
        (* x 2)
        doubled_x
    )
)")]

// multiple raw commands can be inserted.
#![thrust::raw_command("(define-fun is_triple ((x Int) (tripled_x Int)) Bool
    (=
        (* x 3)
        tripled_x
    )
)")]

#[thrust::requires(true)]
#[thrust::ensures(result == 2 * x)]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
}
