//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

// The generic parameter `T` shares the local index `T0` with the enum's own
// type parameter `A`. Reconstructing the enum type from the matched fields used
// to conflate the two, emitting a corrupted `Pair<Int-Int>` datatype instance
// next to the correct `Pair<Int-a0>` (solver: `unification failure`). The enum
// type args are now carried by the flow binding, so the assertion below is
// verified.

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
    assert!(v == 1);
}

fn main() {}