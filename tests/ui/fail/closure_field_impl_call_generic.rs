//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

struct Holder<F> {
    func: F,
}

impl<F> thrust_models::Model for Holder<F> {
    type Ty = Holder<thrust_models::model::Closure<F>>;
}

#[thrust_macros::context]
impl<F: Fn(i64) -> i64> Holder<F> {
    #[thrust_macros::requires(x > 0)]
    #[thrust_macros::ensures(result > 0)]
    fn twice(&self, x: i64) -> i64 {
        x + x
    }
}

// Here the impl's `F` is filled by another generic function's parameter instead
// of a concrete closure, so it stays a type parameter -- of `outer`, not of the
// impl that declared it.
#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result > 0)]
fn outer<G: Fn(i64) -> i64>(g: G, x: i64) -> i64 {
    let h = Holder { func: g };
    h.twice(x)
}

fn main() {
    let _ = outer(|y: i64| y + 1, 0);
}
