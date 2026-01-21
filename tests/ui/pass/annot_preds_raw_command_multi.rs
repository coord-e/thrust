//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

#![feature(custom_inner_attributes)]
#![thrust::raw_command("(define-fun is_double ((x Int) (doubled_x Int)) Bool
    (=
        (* x 2)
        doubled_x
    )
)")]

#![thrust::raw_command("(define-fun is_triple ((x Int) (tripled_x Int)) Bool
    (=
        (* x 3)
        tripled_x
    )
)")]

#[thrust::requires(true)]
#[thrust::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}

#[thrust::require(is_double(x, doubled_x))]
#[thrust::ensures(is_triple(x, result))]
fn triple(x: i64, doubled_x: i64) -> i64 {
    x + doubled_x
}

fn main() {
    let a = 3;
    let double_a = double(a);
    assert!(double_a == 6);
    assert!(triple(a, double_a) == 9);
}
