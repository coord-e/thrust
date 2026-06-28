//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    result.2 == 4
        && result.0[result.1] == 10
        && result.0[result.1 + 1] == 20
        && result.0[result.1 + 2] == 30
        && result.0[result.1 + 3] == 40
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    assert!(!slice.is_empty());
    assert!(*slice.first().unwrap() == 10);
    assert!(*slice.get(1).unwrap() == 20);
    assert!(*<[i32] as std::ops::Index<usize>>::index(slice, 2) == 30);
    assert!(*slice.last().unwrap() == 40);
    assert!(slice.get(4).is_none());
}
