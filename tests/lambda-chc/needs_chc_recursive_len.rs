// A CHC problem that genuinely needs a *recursive function signature* to be
// synthesized, on top of the subsequence lambda.
//
// `mylen` recurses down a slice via `split_first`, and the tail `t` it recurses
// on is a subsequence -- a lambda-backed view. Proving `mylen(s) == s.len()`
// requires the solver to infer the recursive summary `mylen(s) == s.length` and
// to relate the tail view's length (`s.length - 1`) back to `s`. The subsequence
// lambda appears in the clause that forms `t` and passes it to the recursive
// call, so a solver must handle `lambda`s to discharge this.
//
// This is safe (`mylen(s) == s.len()` always holds), so a lambda-capable CHC
// solver should return `sat`. The default Spacer solver returns `unknown`
// because of the `lambda`. Produces `needs_chc_recursive_len.smt2`.
fn mylen(s: &[i32]) -> usize {
    match s.split_first() {
        Some((_, t)) => 1 + mylen(t),
        None => 0,
    }
}

#[thrust::callable]
fn check(s: &[i32]) {
    assert!(mylen(s) == s.len());
}

fn main() {}
