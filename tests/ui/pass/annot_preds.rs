//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust::predicate]
fn is_double(x: i64, doubled_x: i64) -> bool {
    x * 2 == doubled_x
    // "(=(
    //     (* (x 2))
    //     doubled_x
    // ))"
}

#[thrust::requires(true)]
#[thrust::ensures(result == 2 * x)]
// #[thrust::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 6);
    assert!(is_double(a, double(a)));
}
