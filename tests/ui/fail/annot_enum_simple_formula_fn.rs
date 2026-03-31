//@error-in-other-file: Unsat

#[derive(PartialEq)]
pub enum X {
    A(i64),
    B(bool),
}

impl thrust_models::Model for X {
    type Ty = X;
}

#[thrust::formula_fn]
fn _thrust_requires_test(x: X) -> bool {
    x == X::A(1)
}

#[thrust::formula_fn]
fn _thrust_ensures_test(_result: (), _x: X) -> bool {
    true
}

#[allow(path_statements)]
fn test(x: X) {
    #[thrust::requires_path]
    _thrust_requires_test;

    #[thrust::ensures_path]
    _thrust_ensures_test;

    if let X::A(i) = x {
        assert!(i == 2);
    } else {
        loop {}
    }
}

fn main() {
    test(X::A(1));
}
