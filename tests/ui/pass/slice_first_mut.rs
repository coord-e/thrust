//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).1 > 0 && (*result).0[0] == 10
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.first_mut().unwrap() = 11;
    assert!(*slice.first().unwrap() == 11);
}
