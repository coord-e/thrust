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
// *normalized* views `(lambda ((k Int)) (ite (and (<= 0 k) (< k len)) (select arr (+ 1 k)) 0))`.
// Because out-of-range positions are pinned to a shared default, full array equality of the
// two views constrains only the in-range elements (indices >= 1); index 0 stays free. So
// `first`'s mutation to 11 is consistent, the path is *not* vacuous, and `slice[0] == 12` is
// correctly refuted. This program produces `split_first_mut_mutation.smt2`.
//
// (An *unguarded* shift `λk. arr[1 + k]` would be unsound here: array indices range over all
// of Z, so the shift is a bijection and equating two shifted views still forces the whole
// arrays equal -- including index 0. The range guard is what fixes that; see README.md.)
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
