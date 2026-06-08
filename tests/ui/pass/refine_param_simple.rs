//@check-pass

#[thrust_macros::param(x: { v: i32 | v > 0 })]
#[thrust_macros::ret({ r: i32 | r >= x })]
fn f(x: i32) -> i32 {
    x
}

fn main() {}
