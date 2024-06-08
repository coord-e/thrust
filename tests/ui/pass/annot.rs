//@check-pass

#![feature(register_tool)]
#![register_tool(refa)]

#[refa::requires(true)]
#[refa::ensures(result != x)]
fn rand_except(x: i64) -> i64 {
    if x == 0 {
        1
    } else {
        0
    }
}

fn main() {
    assert!(rand_except(1) != 1);
}
