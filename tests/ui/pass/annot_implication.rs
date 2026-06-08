//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

use thrust_models::exists;

#[thrust::trusted]
#[thrust::callable]
fn rand() -> i64 {
    unimplemented!()
}

// Basic implication in a postcondition: when the antecedent holds the
// consequent must too; otherwise the obligation is vacuous.
#[thrust_macros::ensures((x > 0) ==> (result > 0))]
fn f(x: i64) -> i64 {
    if x > 0 {
        x
    } else {
        0
    }
}

// An unparenthesized chain must parse right-associatively, i.e.
// `(x > 10) ==> ((x > 5) ==> (result == 1))`. Left-associative parsing would
// make this unprovable, so this case pins down associativity.
#[thrust_macros::ensures((x > 10) ==> (x > 5) ==> (result == 1))]
fn g(x: i64) -> i64 {
    if x > 5 {
        1
    } else {
        0
    }
}

// Implication nested inside a quantifier's closure body.
#[thrust_macros::ensures(exists(|y: i64| (1 == 1) ==> (result == 2 * y)))]
fn k() -> i64 {
    let x = rand();
    x + x
}

fn main() {}
