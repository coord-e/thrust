//@check-pass

// Companion to reborrow_mut_field_of_aggregate_param for enums: a `&mut`
// reachable through an enum variant. Exercises the enum arm of the
// "needs decomposition" check; binding must flow-decompose so the `&mut`
// pulled out of the enum can be reborrowed.

enum E<'a> {
    A(&'a mut i64),
    B,
}

fn bump(r: &mut i64) {
    *r = 1;
}

fn f(w: E) {
    match w {
        E::A(r) => bump(r),
        E::B => {}
    }
}

fn main() {
    let mut x = 0_i64;
    f(E::A(&mut x));
    assert!(x == 1);
}
