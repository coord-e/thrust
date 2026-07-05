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
#[thrust_macros::ensures(T::p(!x))]
fn repeat<T: A>(x: &mut T, n: u64) {
    let mut i = 0;
    while i < n {
        x.f();
        i += 1;
    }
}

#[derive(PartialEq)]
struct X(i64);

impl thrust_models::Model for X {
    type Ty = X;
}

#[thrust_macros::context]
impl A for X {
    fn f(&mut self) {
        self.0 += 1
    }

    fn g(&mut self) {
        if !(self.0 > 0) { self.0 = 1 - self.0 }
    }

    #[thrust_macros::predicate]
    fn p(self) -> bool {
        "(> (tuple_proj<Int>.0 self_) 0)"; true
    }
}

#[derive(PartialEq)]
struct Y(i64);

impl thrust_models::Model for Y {
    type Ty = Y;
}

#[thrust_macros::context]
impl A for Y {
    fn f(&mut self) {
        self.0 += 1
    }

    fn g(&mut self) {
        if !(self.0 > 0) { self.0 = 1 - self.0 }
    }

    #[thrust_macros::predicate]
    fn p(self) -> bool {
        "(> (tuple_proj<Int>.0 self_) 0)"; true
    }
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(X::p(result.0) && Y::p(result.1))]
fn target() -> (X, Y) {
    let (mut x, mut y) = (X(1), Y(-1));
    repeat(&mut x, 3);
    repeat(&mut y, 5);
    (x, y)
}

fn main() {}
