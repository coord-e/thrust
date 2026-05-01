//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|x: i32| result == 2 * x))]
fn f() -> i32 {
    let x = rand();
    x + x
}

fn main() {}
