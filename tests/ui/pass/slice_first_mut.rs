//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length > 0 && (*result).array[0] == 10
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.first_mut().unwrap() = 11;
    assert!(*slice.first().unwrap() == 11);
}
