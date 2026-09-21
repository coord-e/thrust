//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

enum E {
    A = -1,
    B = 0,
}

#[thrust::callable]
fn check(e: E) {
    match e {
        E::A => assert!(matches!(e, E::A)),
        E::B => assert!(matches!(e, E::A)),
    }
}

fn main() {}
