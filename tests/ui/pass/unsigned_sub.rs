//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(x >= y)]
#[thrust_macros::ensures(result == x - y)]
fn diff(x: u32, y: u32) -> u32 {
    x - y
}

fn main() {}
