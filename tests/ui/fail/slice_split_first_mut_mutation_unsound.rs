//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).2 == 2
        && (*result).0[(*result).1] == 10
        && (*result).0[(*result).1 + 1] == 20
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
