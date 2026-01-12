//@error-in-other-file: invalid attribute
//@compile-flags: -Adead_code -C debug-assertions=off

// Insert definitions written in SMT-LIB2 format into .smt file directly.
// This feature is intended for debug or experiment purpose.
#![feature(custom_inner_attributes)]
#![thrust::raw_define] // argument must be single string literal

#[thrust::requires(true)]
#[thrust::ensures(result == 2 * x)]
// #[thrust::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
    // assert!(is_double(a, double(a)));
}
