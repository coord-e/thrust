//@check-pass
//@compile-flags: -C debug-assertions=off

trait T {
    fn f(b: bool) -> i64;
}

struct A;
struct B;

impl thrust_models::Model for A {
    type Ty = Self;
}

impl thrust_models::Model for B {
    type Ty = Self;
}

impl T for A {
    fn f(b: bool) -> i64 {
        enum E {
            X(i64),
            Y,
        }
        impl thrust_models::Model for E {
            type Ty = Self;
        }
        let e = if b { E::X(1) } else { E::Y };
        match e {
            E::X(x) => x,
            E::Y => 0,
        }
    }
}

impl T for B {
    fn f(b: bool) -> i64 {
        enum E {
            Z(bool),
            W(i64),
        }
        impl thrust_models::Model for E {
            type Ty = Self;
        }
        let e = if b { E::Z(true) } else { E::W(5) };
        match e {
            E::Z(_) => 10,
            E::W(v) => v,
        }
    }
}

fn main() {
    assert!(A::f(true) == 1);
    assert!(B::f(false) == 5);
}
