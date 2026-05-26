//@check-pass
//@compile-flags: -C debug-assertions=off

// A refinement on a `Box` (owned pointer) pointee in return position must be
// enforced soundly. Here the pointee value `n` satisfies the precondition
// `n > 0`, so the returned `Box<{v | v > 0}>` is valid and verification passes.

#[thrust::formula_fn]
fn _thrust_requires_mk(n: i64) -> bool {
    n > 0
}

#[thrust::ret(Box<{v: int | v > 0}>)]
fn mk(n: i64) -> Box<i64> {
    #[thrust::requires_path]
    _thrust_requires_mk;
    Box::new(n)
}

fn main() {
    let _b = mk(7);
}
