//@check-pass
//@compile-flags: -C debug-assertions=off

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_requires_incr(m: thrust_models::model::Mut<i64>, x: i64) -> bool {
    true
}

#[allow(unused_variables)]
#[thrust::formula_fn]
fn _thrust_ensures_incr(result: (), m: thrust_models::model::Mut<i64>, x: i64) -> bool {
    !m == *m + x
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
