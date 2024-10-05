//@check-pass
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(thrust)]

pub enum X {
    A(i64),
    B(bool),
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> X { unimplemented!() }

fn inv(x: &mut X) {
    match x {
        X::A(i) => *i = -*i,
        X::B(b) => *b = !*b,
    }
}

fn is_pos(x: &X) -> bool {
    match x {
        X::A(i) => *i > 0,
        X::B(b) => *b,
    }
}

fn main() {
    let mut x = rand();
    if is_pos(&x) {
        inv(&mut x); 
        assert!(!is_pos(&x));
    }
}
