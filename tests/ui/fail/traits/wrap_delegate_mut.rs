//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self))]
    #[thrust_macros::ensures(Self::p(!self))]
    fn f(&mut self);

    #[thrust_macros::requires(Self::p(*self))]
    fn g(&mut self);

    #[thrust_macros::predicate]
    fn p(self) -> bool;
}

struct W<I> {
    inner: I,
}

impl<I> thrust_models::Model for W<I> {
    type Ty = W<I>;
}

#[thrust_macros::context]
impl<I> A for W<I>
where
    I: A + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        // I::p(self.inner)
        "(q_p_39ba461a1ee0ac85e4d6462c04277d68<a0> (tuple_proj<a0>.0 self_))";
        true
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        self.inner.g()
    }
}

fn main() {}
