//@check-pass
//@compile-flags: -C debug-assertions=off

enum E {
    A = 1,
    B,
    C,
}

#[thrust::callable]
fn check(e: E) {
    match e {
        E::A => assert!(matches!(e, E::A)),
        E::B => assert!(matches!(e, E::B)),
        E::C => assert!(matches!(e, E::C)),
    }
}

fn main() {}
