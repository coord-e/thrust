//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }

const HALF_MIN: i32 = i32::MIN / 2;
const HALF_MAX: i32 = i32::MAX / 2;

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(exists(|x: i32| result == 2 * x))]
fn f() -> i32 {
    let x = rand();
    if HALF_MIN <= x && x <= HALF_MAX {
        x + x
    } else {
        0
    }
}

fn main() {}
