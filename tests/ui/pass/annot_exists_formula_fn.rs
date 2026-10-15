//@check-pass
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }

const HALF_MIN: i32 = i32::MIN / 2;
const HALF_MAX: i32 = i32::MAX / 2;

#[thrust::formula_fn]
fn _thrust_requires_f() -> bool {
    true
}

#[thrust::formula_fn]
fn _thrust_ensures_f(result: i32) -> bool {
    thrust_models::exists(|x: i32| result == 2 * x)
}

#[allow(path_statements)]
fn f() -> i32 {
    #[thrust::requires_path]
    _thrust_requires_f;

    #[thrust::ensures_path]
    _thrust_ensures_f;

    let x = rand();
    if HALF_MIN <= x && x <= HALF_MAX {
        x + x
    } else {
        0
    }
}

fn main() {}
