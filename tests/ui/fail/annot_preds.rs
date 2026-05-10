//@error-in-other-file: Unsat
//@no-rustfix
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust::predicate]
fn is_double(x: thrust_models::model::Int, doubled_x: thrust_models::model::Int) -> bool {
    "(=
        (* x 2)
        doubled_x
    )"; true
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(is_double(x, result))]
fn double(x: i64) -> i64 {
    x + x + x
}

fn main() {
    let a = 3;
    assert!(double(a) == 9);
}
