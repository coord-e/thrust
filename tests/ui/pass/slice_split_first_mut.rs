//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[0] == 10
        && (*result).array[1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    {
        let (boundary, rest) = slice.split_first_mut().unwrap();
        *boundary = 11;
        *rest.first_mut().unwrap() = 21;
    }
    assert!(slice[0] == 11);
    assert!(slice[1] == 21);
}
