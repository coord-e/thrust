//@error-in-other-file: Unsat
//@compile-flags: -Aunused_parens -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

struct S<F> {
    func: F,
}

impl<F> thrust_models::Model for S<F> {
    type Ty = S<thrust_models::model::Closure<F>>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> S<F> {
    #[thrust_macros::requires(thrust_macros::pre!(((*self).func)(v)))]
    #[thrust_macros::ensures(thrust_macros::post!(((*self).func)(v), result))]
    fn call(&self, v: i64) -> i64 {
        (self.func)(v) + 1
    }
}

fn main() {}
