//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// KNOWN LIMITATION: mutation through a `&mut` returned inside a tuple (as
// `split_first_mut` does) does not currently propagate back to the original
// slice, which is unsound. This test is expected to be rejected (`Unsat`) once
// that is fixed; it is kept here as a reproduction until the fix lands.
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
    {
        // Destructure the returned tuple, then mutate through its first reference.
        let (first, _tail) = slice.split_first_mut().unwrap();
        *first = 11;
    }
    // The mutation makes slice[0] equal to 11, so this must be rejected.
    assert!(slice[0] == 12);
}
