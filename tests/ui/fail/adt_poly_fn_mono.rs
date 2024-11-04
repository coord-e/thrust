//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(thrust)]

pub enum X<T> {
    A(T),
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> X<i32> { unimplemented!() }

fn inv(x: X<i32>) -> X<i32> {
    match x {
        X::A(i) => X::A(-i),
    }
}

fn is_pos(x: &X<i32>) -> bool {
    match x {
        X::A(i) => *i > 0,
    }
}

fn pos() -> X<i32> {
    let x = rand();
    if !is_pos(&x) { loop {} }
    x
}

fn main() {
    let x = pos();
    assert!(is_pos(&inv(x)));
}
