//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

struct Holder<F> {
    func: F,
}

impl<F> thrust_models::Model for Holder<F> {
    type Ty = Holder<thrust_models::model::Closure<F>>;
}

// The `Fn` bound sits on the impl block rather than on the method, so a call
// from outside has to resolve `F` at the arguments the caller supplies. The body
// deliberately leaves the closure alone: calling it would drag in its own
// precondition, which is a separate question.
#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Holder<F> {
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(result > 0)]
    fn twice(&self, x: i64) -> i64 {
        x + x
    }
}

fn main() {
    let h = Holder { func: |y: i64| y + 1 };
    let _ = h.twice(1);
}
