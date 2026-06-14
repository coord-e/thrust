//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self, !self, x))]
    #[thrust_macros::ensures(Self::p(*self, !self, result))]
    fn f(&mut self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(self, after: Self, x: i64) -> bool;
}

// impl thrust_models::Model for A {
//     type Ty = A;
// }

#[thrust_macros::requires(T::p(*a, !a, x))]
#[thrust_macros::ensures(T::p(*a, !a, result))]
fn target<T: A>(a: &mut T, x: i64) -> i64 {
    let mut v = x;
    let mut i = 0;
    while i < 3 {
        v = a.f(v);
        i += 1;
    }

    v
}

fn main() {}
