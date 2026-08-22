//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length > 1 && (*result).array[(*result).offset + 1] == 20
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.get_mut(1).unwrap() = 21;
    assert!(*slice.get(1).unwrap() == 22);
}
