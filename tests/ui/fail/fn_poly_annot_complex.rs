//@error-in-other-file: Unsat

#[thrust::requires((x.0 > 0) && (x.1 > 0))]
#[thrust::ensures((result.0 == x.1) && (result.1 == x.0))]
fn swap_positive<T, U>(x: (i32, i32, T, U)) -> (i32, i32, U, T) {
    (x.1, x.0, x.3, x.2)
}

fn main() {
    let result = swap_positive((-5, 10, true, 42));
    assert!(result.0 == 10);
}
