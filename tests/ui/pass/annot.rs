//@check-pass

#![feature(register_tool)]
#![register_tool(thrust)]

#[thrust::requires(true)]
#[thrust::ensures(result != x)]
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
