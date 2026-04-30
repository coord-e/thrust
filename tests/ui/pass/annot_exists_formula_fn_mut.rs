//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_requires_incr(m: thrust_models::model::Mut<i32>, x: i32) -> bool {
    x > 0
}

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_ensures_incr(result: (), m: thrust_models::model::Mut<i32>, x: i32) -> bool {
    thrust_models::exists(|y: i32| !m == y && y > *m)
}

#[allow(path_statements)]
fn incr(m: &mut i32, x: i32) {
    #[thrust::requires_path]
    _thrust_requires_incr;
    #[thrust::ensures_path]
    _thrust_ensures_incr;

    *m += x;
}

fn main() {
    let mut a = 0;
    incr(&mut a, 1);
    assert!(a > 0);
}
