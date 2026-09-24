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

struct M<I, F> {
    iter: I,
    func: F,
}

impl<I, F> thrust_models::Model for M<I, F> {
    type Ty = M<I, F>;
}

#[thrust_macros::context]
impl<I, F> A for M<I, F>
where
    I: A + thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
    F: FnMut(i64) -> i64,
{
    #[thrust_macros::predicate]
    fn p(self) -> bool {
        // I::p(self.iter)
        "(q_p_90849721ed499bdbe024ffd3cd1c5364<a0> (tuple_proj<a0-a1>.0 self_))";
        true
    }

    fn g(&mut self) {}

    fn f(&mut self) {
        self.iter.g()
    }
}

fn main() {}
