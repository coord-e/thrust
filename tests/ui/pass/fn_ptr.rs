//@check-pass
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(refa)]

#[refa::requires(true)]
#[refa::ensures(true)]
fn rand() -> i64 { 0 }

fn incr(m: &mut i64) {
    *m += 1;
}

fn app(f: fn(&mut i64), mut x: i64) -> i64 {
    f(&mut x);
    x
}

fn main() {
    let i = rand();
    let x = app(incr, i);
    assert!(x == i + 1);
}
