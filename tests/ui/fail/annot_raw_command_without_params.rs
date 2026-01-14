//@compile-flags: -Adead_code -C debug-assertions=off
// This test panics with "invalid attribute" for now.
// TODO: reporting rustc diagnostics for parse errors

// Insert commands written in SMT-LIB2 format into .smt file directly.
// This feature is intended for debug or experiment purpose.
#![feature(custom_inner_attributes)]
#![thrust::raw_command] // argument must be single string literal

#[thrust::requires(true)]
#[thrust::ensures(result == 2 * x)]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
}
