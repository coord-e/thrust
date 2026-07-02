// A read-only use of `<[T]>::split_first_mut`: split the slice, then observe the
// boundary element and the tail view. Verifying this program is safe.
//
// The tail is modeled with `Seq::subsequence`, which is backed by a shifted-array
// lambda (`Term::ArrayShift`). This program is what produces `split_first_mut.smt2`.
//
// It cannot be checked by the default Spacer solver because the generated CHC uses
// SMT-LIB `lambda`s over arrays, which no CHC solver we target supports yet. It is a
// hand-off test case for developing that solver support; see README.md.
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
    let (first, tail) = slice.split_first_mut().unwrap();
    assert!(*first == 10);
    assert!(tail.len() == 1);
    assert!(*tail.first().unwrap() == 20);
}
