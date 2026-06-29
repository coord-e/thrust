//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self))]
    #[thrust_macros::ensures(Self::p(!self))]
    fn f(&mut self);
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(Self::p(!self))]
    fn g(&mut self);

    #[thrust_macros::predicate]
    fn p(self) -> bool;
}

#[thrust_macros::requires(T::p(*x) && n > 0)]
#[thrust_macros::ensures(T::p(!x) && S::p(!y))]
fn multi_loop<'a, T: A, S: A>(x: &mut T, y: &mut S, n: u64) {
    let mut i = 0;
    while i < n { // The loop depends on P
        x.f(); i += 1;
    }

    let mut j = 0;
    while j < n { // The loop depends on Q
        y.g(); j += 1;
    }
}

fn main() {}
