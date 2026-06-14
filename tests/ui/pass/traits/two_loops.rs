//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::p(*result))]
    fn f(&self) -> &Self;
    #[thrust_macros::requires(Self::q(*self))]
    #[thrust_macros::ensures(Self::q(*result))]
    fn g(&self) -> &Self;

    #[thrust_macros::predicate]
    fn p(self) -> bool;
    #[thrust_macros::predicate]
    fn q(self) -> bool;
}

#[thrust_macros::requires(T::q(*y))]
#[thrust_macros::ensures(T::p(*result.0) && T::q(*result.1))]
fn target<'a, T: A>(x: &'a T, y: &'a T) -> (&'a T, &'a T) {
    let mut v = x;
    let mut w = y;
    let mut i = 0;
    while i < 3 { // The loop depends on P
        v = v.f();
        i += 1;
    }

    let mut j = 0;
    while j < 3 { // The loop depends on Q
        w = w.g();
        j += 1;
    }

    (v, w)
}

fn main() {}
