//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() == 2
        && (*result)[0] == 10
        && (*result)[1] == 20
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    let (boundary, rest) = slice.split_first().unwrap();
    assert!(*boundary == 99);
    assert!(rest.len() == 1);
    assert!(*rest.first().unwrap() == 20);
}
