//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

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

fn main() {
    let slice = slice();
    {
        let (first, _tail) = slice.split_first_mut().unwrap();
        *first = 11;
    }
    assert!(slice[0] == 11);
    assert!(slice[1] == 20);
}
