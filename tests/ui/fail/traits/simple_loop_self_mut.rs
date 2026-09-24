//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self, x))]
    #[thrust_macros::ensures(Self::p(!self, result))]
    fn f(&mut self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(self, x: i64) -> bool;
}

#[thrust_macros::context]
#[thrust_macros::requires(T::p(*a, x))]
#[thrust_macros::ensures(T::p(!a, result))]
fn target<T: A>(a: &mut T, x: i64) -> i64 {
    let b = a;
    let mut v = x;
    let mut i = 0;
    while i < 3 {
        thrust_macros::invariant!(
            |b: &mut T, v: i64, a: thrust_models::FnParam<&mut T>|
            T::p(*b, v) && !b == !a.at_entry()
        );
        v = b.f(v) + 1;
        i += 1;
    }

    v
}

fn main() {}
