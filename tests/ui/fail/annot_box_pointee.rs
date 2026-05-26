//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A refinement on a `Box` (owned pointer) pointee in return position must be
// enforced soundly. Here the body returns `Box::new(-1)`, which violates the
// declared `Box<{v | v > 0}>`, so verification must fail.

#[thrust::ret(Box<{v: int | v > 0}>)]
fn mk() -> Box<i64> {
    Box::new(-1)
}

fn main() {
    let _b = mk();
}
