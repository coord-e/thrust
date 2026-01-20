//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

#![feature(custom_inner_attributes)]
#![thrust::raw_command("(define-fun is_double ((x Int) (doubled_x Int)) Bool
    (=
        (* x 2)
        doubled_x
    )
)")]

#[thrust::requires(true)]
#[thrust::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
}