//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).2 > 2 && (*result).0[(*result).1 + 2] == 40
)]
fn slice() -> &'static mut [i32] {
    unimplemented!()
}

fn main() {
    let slice = slice();
    *<[i32] as std::ops::IndexMut<usize>>::index_mut(slice, 2) = 41;
    assert!(*<[i32] as std::ops::Index<usize>>::index(slice, 2) == 42);
}
