// A CHC problem whose *recursive function summary* is load-bearing on the
// subsequence lambda -- not just its length.
//
// `nth` recurses down the slice with `split_first`, recursing on the tail view
// `t` (a lambda-backed subsequence). To discharge `nth(s, 1) == s[1]`, a solver
// must synthesize the summary
//
//     nth(s, n) == s.array[n]        (for 0 <= n < s.len())
//
// which constrains the *array element* at index `n`, not the length. Closing the
// recursive step is where the lambda becomes essential: the recursive call is
// `nth(t, n-1)` with `t.array = subsequence(s, 1, len).array`, so the solver must
// establish
//
//     select(subsequence(s,1,len).array, n-1) == select(s.array, n)
//
// i.e. it must reason about `select` applied to the guarded subsequence lambda.
// A summary that tracked only lengths cannot prove this goal.
//
// This is safe, so a lambda-capable CHC solver should return `sat`; the default
// Spacer solver returns `unknown`. Produces `needs_chc_recursive_nth.smt2`.
fn nth(s: &[i32], n: usize) -> i32 {
    match s.split_first() {
        Some((h, t)) => {
            if n == 0 {
                *h
            } else {
                nth(t, n - 1)
            }
        }
        None => 0,
    }
}

#[thrust::callable]
fn check(s: &[i32]) {
    if s.len() >= 2 {
        assert!(nth(s, 1) == s[1]);
    }
}

fn main() {}
