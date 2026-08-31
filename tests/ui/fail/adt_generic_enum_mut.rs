//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// Same structure as the pass counterpart, except the assertion is false: the
// matched field has value `1`, so `assert!(v == 0)` must be rejected as
// unsatisfiable. Before the fix, the corrupted enum type reconstruction made
// the solver fail with `unification failure` instead of returning Unsat.

enum Pair<A, B> {
    L(A),
    R(B),
}

struct Wrap<T> {
    p: Pair<u32, T>,
}

#[thrust::callable]
fn check<T>() {
    let mut w: Wrap<T> = Wrap { p: Pair::L(1u32) };
    let v = match &mut w.p {
        Pair::L(x) => *x,
        Pair::R(_) => unimplemented!(),
    };
    assert!(v == 0);
}

fn main() {}