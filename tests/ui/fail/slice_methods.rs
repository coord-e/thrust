//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[0] == 10
        && (*result).array[1] == 20
)]
fn slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    assert!(*slice.last().unwrap() == 10);
}
