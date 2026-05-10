//@error-in-other-file: Unsat
//@no-rustfix

#[thrust::formula_fn]
fn _thrust_requires_rand_except(x: i64) -> bool {
    true
}

#[thrust::formula_fn]
fn _thrust_ensures_rand_except(result: i64, x: i64) -> bool {
    result != x
}

fn rand_except(x: i64) -> i64 {
    #[thrust::requires_path]
    _thrust_requires_rand_except;
    #[thrust::ensures_path]
    _thrust_ensures_rand_except;

    if x == 0 {
        1
    } else {
        0
    }
}

#[thrust::formula_fn]
fn _thrust_requires_f(x: i64) -> bool {
    true
}

#[thrust::formula_fn]
fn _thrust_ensures_f(result: i64, x: i64) -> bool {
    (result == 1) || (result == -1) && result == 0
}

fn f(x: i64) -> i64 {
    #[thrust::requires_path]
    _thrust_requires_f;
    #[thrust::ensures_path]
    _thrust_ensures_f;

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
    assert!(rand_except(1) == 0);
}
