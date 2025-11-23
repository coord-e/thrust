//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::requires((n > 0) && (m > 0))]
#[thrust::ensures((result.0 == m) && (result.1 == n))]
fn swap_pair<T>(n: i32, m: i32, _phantom: T) -> (i32, i32) {
    (m, n)
}

fn main() {
    let result = swap_pair(5, 10, true);
    assert!(result.0 == 10);
    assert!(result.1 == 5);
}
