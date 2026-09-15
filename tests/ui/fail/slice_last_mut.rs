//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).len() > 0
        && (*result)[(*result).len() - 1] == 30
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *slice.last_mut().unwrap() = 31;
    assert!(*slice.last().unwrap() == 32);
}
