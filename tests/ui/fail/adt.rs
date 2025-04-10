//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

pub enum X {
    A(i64),
    B(bool),
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
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
        assert!(is_pos(&inv(x)));
    }
}
