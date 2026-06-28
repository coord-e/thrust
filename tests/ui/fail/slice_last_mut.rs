//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).1 > 0
        && (*result).0[(*result).1 - 1] == 30
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.last_mut().unwrap() = 31;
    assert!(*slice.last().unwrap() == 32);
}
