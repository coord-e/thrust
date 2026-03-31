//@check-pass

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_requires_swap(x: thrust_models::model::Mut<i64>, y: i64) -> bool {
    true
}

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_ensures_swap(result: (), x: thrust_models::model::Mut<i64>, y: thrust_models::model::Mut<i64>) -> bool {
    !x == *y && !y == *x
}

#[allow(path_statements)]
fn swap<T>(x: &mut T, y: &mut T) {
    #[thrust::requires_path]
    _thrust_requires_swap;

    #[thrust::ensures_path]
    _thrust_ensures_swap;

    std::mem::swap(x, y)
}

fn main() {
    let mut a = 1;
    let mut b = 2;
    swap(&mut a, &mut b);
    assert!(a == 2 && b == 1);
}
