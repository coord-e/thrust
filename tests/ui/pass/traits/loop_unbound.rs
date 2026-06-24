//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(x))]
    #[thrust_macros::ensures(Self::p(result))]
    fn f(&self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(x: i64) -> bool;
}

#[thrust_macros::requires(T::p(x))]
#[thrust_macros::ensures(T::p(result))]
fn target<T: A>(a: &T, x: i64, n: u64) -> i64 {
    let mut v = x;
    let mut i = 0;
    while i < n {
        v = a.f(v);
        i += 1;
    }

    v
}

fn main() {}
