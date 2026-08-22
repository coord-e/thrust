//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length > 0
        && (*result).array[(*result).offset + (*result).length - 1] == 30
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.last_mut().unwrap() = 31;
    assert!(*slice.last().unwrap() == 31);
}
