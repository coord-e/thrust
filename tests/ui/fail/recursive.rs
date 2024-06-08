//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#![feature(register_tool)]
#![register_tool(refa)]

#[refa::requires(true)]
#[refa::ensures(true)]
fn rand() -> i64 { 0 }

fn sum(i: i64) -> i64 {
    if i == 0 {
        0
    } else {
        sum(i - 1) + 1
    }
}

fn main() {
    let x = rand();
    let y = sum(x);
    assert!(y == x + 1);
}
