//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A refinement on a `Box` (owned pointer) pointee in return position must be
// enforced soundly. The parameter is pinned with `thrust::param` to a
// satisfiable refinement (so the precondition cannot be inferred away). The
// body ignores `n` and returns `Box::new(-1)`, which violates the declared
// `Box<{v | v > 0}>`, so verification must fail.

#[thrust::param(n: {v: int | v > 0})]
#[thrust::ret(Box<{v: int | v > 0}>)]
fn mk(n: i64) -> Box<i64> {
    Box::new(-1)
}

fn main() {
    let _b = mk(7);
}
