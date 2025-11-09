//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::requires(x > 0)]
#[thrust::ensures((result == x) && (result > 0))]
fn pass_positive<T>(x: i32, _dummy: T) -> i32 {
    x
}

fn main() {
    let result = pass_positive(-5, true);
    assert!(result == -5);
}
