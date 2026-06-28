//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).1 > 1 && (*result).0[1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.get_mut(1).unwrap() = 21;
    assert!(*slice.get(1).unwrap() == 21);
}
