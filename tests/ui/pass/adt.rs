//@check-pass
//@compile-flags: -C debug-assertions=off

pub enum X {
    A(i64),
    B(bool),
}

impl thrust_models::Model for X {
    type Ty = Self;
}

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn rand() -> X { unimplemented!() }

fn inv(x: X) -> X {
    match x {
        X::A(i) => X::A(-i),
        X::B(b) => X::B(!b),
    }
}

fn is_pos(x: &X) -> bool {
    match x {
        X::A(i) => *i > 0,
        X::B(b) => *b,
    }
}

fn main() {
    let x = rand();
    if is_pos(&x) {
        assert!(!is_pos(&inv(x)));
    }
}
