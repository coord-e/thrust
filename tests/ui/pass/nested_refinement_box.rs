//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(n: { v: i32 | v >= 0 })]
#[thrust_macros::ret(Box<{ v: i32 | v >= 0 }>)]
fn make(n: i32) -> Box<i32> {
    Box::new(n)
}

#[thrust_macros::param(x: Box<{ v: i32 | v >= 0 }>)]
#[thrust_macros::ret(Box<{ v: i32 | v >= 0 }>)]
fn identity(mut x: Box<i32>) -> Box<i32> {
    *x = 1;
    x
}

fn main() {
    assert!(*identity(make(0)) >= 0);
}
