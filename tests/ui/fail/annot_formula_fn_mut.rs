//@error-in-other-file: Unsat

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_requires_incr(m: thrust_models::model::Mut<i64>, x: i64) -> bool {
    -1000 <= *m && *m <= 1000 && -1000 <= x && x <= 1000
}

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_ensures_incr(result: (), m: thrust_models::model::Mut<i64>, x: i64) -> bool {
    !m == *m + 1
}

#[allow(path_statements)]
fn incr(m: &mut i64, x: i64) {
    #[thrust::requires_path]
    _thrust_requires_incr;
    #[thrust::ensures_path]
    _thrust_ensures_incr;

    *m += x;
}

fn main() {
    let mut x = 0;
    incr(&mut x, 1);
    incr(&mut x, 1);
    assert!(x == 2);
}
