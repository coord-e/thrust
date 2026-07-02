//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[(*result).offset] == 10
        && (*result).array[(*result).offset + 1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    let (last, _init) = slice.split_last_mut().unwrap();
    // wrong: the last element is 20, not 21
    assert!(*last == 21);
}
