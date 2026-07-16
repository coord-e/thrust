//@check-pass
//@compile-flags: -C debug-assertions=off

// A hand-written `PartialEq` impl consistent with structural equality is checked against the
// trait method's spec and accepted, so `x == x` holds.

enum X {
    A(i32),
}

impl thrust_models::Model for X {
    type Ty = Self;
}

impl PartialEq for X {
    fn eq(&self, other: &X) -> bool {
        match (self, other) {
            (Self::A(lhs), Self::A(rhs)) => lhs.eq(rhs),
        }
    }
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn rand() -> X {
    unimplemented!()
}

fn main() {
    let x = rand();
    assert!(x == x);
}
