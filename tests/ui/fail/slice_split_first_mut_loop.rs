//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper
//@rustc-env: THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() == 2
        && (*result)[0] == 10
        && (*result)[1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

#[thrust::callable]
fn check() {
    let sl = slice();
    let mut s = &mut *sl;
    while let Some((first, rest)) = s.split_first_mut() {
        *first = 0;
        s = rest;
    }
    assert!(sl[0] != 0);
}

fn main() {}
