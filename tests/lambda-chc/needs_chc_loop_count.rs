// A CHC problem that genuinely needs a *loop invariant* to be synthesized, on
// top of the subsequence lambda.
//
// The loop walks `slice` by repeatedly peeling off the first element with
// `split_first`, rebinding `s` to the tail subsequence each iteration. Proving
// `count == slice.len()` after the loop needs the invariant
// `count + s.len() == slice.len()`. The loop-carried `s` is a subsequence (a
// lambda-backed view, and a nested one after several iterations), so the
// invariant predicate ranges over `lambda`-valued state -- a solver must handle
// `lambda`s to find it.
//
// This is safe, so a lambda-capable CHC solver should return `sat`. The default
// Spacer solver returns `unknown` because of the `lambda`. Produces
// `needs_chc_loop_count.smt2`.
#[thrust::callable]
fn check(slice: &[i32]) {
    let mut s = slice;
    let mut count = 0;
    while let Some((_, rest)) = s.split_first() {
        count += 1;
        s = rest;
    }
    assert!(count == slice.len());
}

fn main() {}
