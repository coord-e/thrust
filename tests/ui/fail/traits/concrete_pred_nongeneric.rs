//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait A {
    #[thrust_macros::predicate]
    fn p(self) -> bool;
}

#[derive(PartialEq)]
struct X(i64);

impl thrust_models::Model for X {
    type Ty = X;
}

#[thrust_macros::context]
impl A for X {
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        "(> (tuple_proj<Int>.0 self_) 0)"; true
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(X::p(result))]
fn target() -> X {
    X(0)
}

fn main() {}
