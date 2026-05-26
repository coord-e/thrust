//@check-pass
//@compile-flags: -C debug-assertions=off

// A refinement on a `Box` (owned pointer) pointee in return position must be
// enforced soundly. The parameter is pinned with `thrust::param` (otherwise an
// unannotated parameter receives a fresh, inferable predicate). Here the
// returned pointee value `n` satisfies `n > 0`, so the declared
// `Box<{v | v > 0}>` holds and verification passes.

#[thrust::param(n: {v: int | v > 0})]
#[thrust::ret(Box<{v: int | v > 0}>)]
fn mk(n: i64) -> Box<i64> {
    Box::new(n)
}

fn main() {
    let _b = mk(7);
}
