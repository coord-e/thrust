//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 4
        && (*result).array[(*result).offset] == 10
        && (*result).array[(*result).offset + 1] == 20
        && (*result).array[(*result).offset + 2] == 30
        && (*result).array[(*result).offset + 3] == 40
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
