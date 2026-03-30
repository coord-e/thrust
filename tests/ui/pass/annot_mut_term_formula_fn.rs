//@check-pass

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_requires_f(x: thrust_models::model::Mut<i64>, y: i64) -> bool {
    true
}

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_ensures_f(result: (), x: thrust_models::model::Mut<i64>, y: i64) -> bool {
    x == thrust_models::model::Mut::new(*x, y)
}

#[allow(path_statements)]
fn f(x: &mut i64, y: i64) {
    #[thrust::requires_path]
    _thrust_requires_f;

    #[thrust::ensures_path]
    _thrust_ensures_f;

    *x = y;
}

fn main() {
    let mut a = 1;
    f(&mut a, 2);
    assert!(a == 2);
}
