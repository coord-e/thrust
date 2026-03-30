//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i32 { unimplemented!() }

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
    x + x
}

fn main() {}
