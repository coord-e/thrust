//@check-pass

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn sum(i: i64) -> i64 {
    if i == 0 {
        0
    } else {
        sum(i - 1) + 1
    }
}

fn main() {
    let x = rand();
    if 0 <= x && x <= i64::MAX {
        let y = sum(x);
        assert!(y == x);
    }
}
