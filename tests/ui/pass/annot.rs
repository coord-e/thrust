//@check-pass

#[thrust::requires(true)]
#[thrust::ensures(result != x)]
fn rand_except(x: i64) -> i64 {
    if x == 0 {
        1
    } else {
        0
    }
}

#[thrust::requires(true)]
#[thrust::ensures((result == 1) || (result == -1))]
fn f(x: i64) -> i64 {
    let y = rand_except(x);
    if y > x {
        1
    } else if y < x {
        -1
    } else {
        0
    }
}

fn main() {
    assert!(rand_except(1) != 1);
}
