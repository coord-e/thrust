//@check-pass
//@compile-flags: -C debug-assertions=off
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[(*result).offset] == 10
        && (*result).array[(*result).offset + 1] == 20
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    let (first, tail) = slice.split_first().unwrap();
    assert!(*first == 10);
    assert!(tail.len() == 1);
    assert!(*tail.first().unwrap() == 20);
}
