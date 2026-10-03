//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=1
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() == 3
        && (*result)[0] == 10
        && (*result)[1] == 20
        && (*result)[2] == 30
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn last(slice: &[i32]) -> i32 {
    slice[slice.len() - 1]
}

fn main() {
    let slice = slice();
    assert!(last(slice) == 30);
}
