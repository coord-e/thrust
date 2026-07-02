// Soundness reproduction for `<[T]>::split_first_mut`.
//
// This is the program that #164 recorded as `slice_split_first_mut_mutation_unsound.rs`:
// split the slice, mutate the boundary element through the returned `&mut`, drop the
// (unused) tail, then make a false claim about the original slice. `slice[0]` becomes
// 11, so `assert!(slice[0] == 12)` must be rejected (`Unsat`).
//
// Under the offset-sharing subsequence model of #163/#164 this was *vacuously accepted*:
// dropping the unmutated tail resolved its prophecy with `final == current` over two
// subsequence triples that still carried the whole backing array, forcing
// `(!slice).array == (*slice).array` at every index — including index 0, which belongs
// to `first`. Together with `first`'s resolved final (`= 11`) and the initial state
// (`= 10`) the path became contradictory, so every assertion (even `assert!(false)`) was
// discharged vacuously.
//
// With the lambda-backed subsequence, the tail's `final == current` equates two
// `(lambda ((i Int)) (select arr (+ 1 i)))` views, which only constrains indices >= 1.
// Index 0 stays free, so `first`'s mutation to 11 is consistent, the path is *not*
// vacuous, and `slice[0] == 12` is correctly refuted. This program produces
// `split_first_mut_mutation.smt2`.
#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(
    (*result).length == 2
        && (*result).array[0] == 10
        && (*result).array[1] == 20
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
