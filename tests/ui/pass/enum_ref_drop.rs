//@check-pass
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(thrust)]

pub enum X<'a, 'b> {
    A(&'a mut i64),
    B(&'b mut i64),
}

#[thrust::trusted]
#[thrust::requires(true)]
#[thrust::ensures(true)]
fn rand() -> i64 { unimplemented!() }

fn x(i: &mut i64) -> X {
    if *i >= 0 {
        X::A(i)
    } else {
        X::B(i)
    }
}

fn main() {
    let mut i = rand();
    match x(&mut i) {
        X::A(a) => *a += 1,
        X::B(b) => *b = -*b,
    }
    assert!(i > 0);
}
