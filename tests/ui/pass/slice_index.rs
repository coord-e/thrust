//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.2 == 2
        && result.0[result.1] == 10
        && result.0[result.1 + 1] == 20
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    assert!(slice.len() == 2);
    assert!(slice[0] == 10);
    assert!(slice[1] == 20);
}
