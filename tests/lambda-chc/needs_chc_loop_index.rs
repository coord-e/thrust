// A CHC problem whose *loop invariant* is load-bearing on the subsequence
// lambda -- not just its length.
//
// The loop walks `slice` by peeling the first element with `split_first`,
// rebinding `s` to the tail view and advancing `i`. To discharge the in-loop
// assertion `*first == slice[i]`, a solver must synthesize the invariant
//
//     s == slice.subsequence(i, slice.len())
//
// Its array component is `s.array == subsequence(slice, i, len).array`, i.e. the
// invariant *contains a guarded subsequence lambda whose shift is the loop
// counter `i`*. Under that invariant, `*first == s.array[0] == slice.array[i] ==
// slice[i]`. An invariant that tracked only lengths (as `needs_chc_loop_count`
// used to) cannot relate `first` to `slice[i]`, so the lambda is essential here.
//
// This is safe, so a lambda-capable CHC solver should return `sat`; the default
// Spacer solver returns `unknown`. Produces `needs_chc_loop_index.smt2`.
#[thrust::callable]
fn check(slice: &[i32]) {
    let mut s = slice;
    let mut i = 0;
    while i < slice.len() {
        if let Some((first, rest)) = s.split_first() {
            assert!(*first == slice[i]);
            s = rest;
            i += 1;
        } else {
            break;
        }
    }
}

fn main() {}
