//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

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

#[thrust_macros::context]
#[thrust_macros::requires(n > 0)]
#[thrust_macros::ensures(T::p(!x) && S::p(!y))]
fn multi_loop<'a, T: A, S: A>(x: &mut T, y: &mut S, n: u64) {
    let a = x;
    let b = y;

    let mut i = 0;
    while i < n { // The loop depends on P
        thrust_macros::invariant!(
            |a: &mut T, b: &mut S, x: thrust_models::FnParam<&mut T>, y: thrust_models::FnParam<&mut S>, n: u64|
            n > 0 && T::p(*a) && !a == !x.at_entry() && !b == !y.at_entry()
        );
        a.f(); i += 1;
    }

    let mut j = 0;
    while j < n { // The loop depends on Q
        thrust_macros::invariant!(
            |b: &mut S, x: thrust_models::FnParam<&mut T>, y: thrust_models::FnParam<&mut S>, j: u64, n: u64|
            n > 0 && T::p(!x.at_entry()) && (j > 0 ==> S::p(*b)) && !b == !y.at_entry()
        );
        b.g(); j += 1;
    }
}

fn main() {}
