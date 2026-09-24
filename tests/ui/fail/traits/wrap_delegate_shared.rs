//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait A {
    #[thrust_macros::requires(Self::p(*self, x))]
    #[thrust_macros::ensures(Self::p(*self, result))]
    fn f(&self, x: i64) -> i64;

    #[thrust_macros::requires(Self::p(*self, x))]
    fn g(&self, x: i64) -> i64;

    #[thrust_macros::predicate]
    fn p(self, x: i64) -> bool;
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
    fn p(self, x: i64) -> bool {
        // I::p(self.inner, x)
        "(q_p_76f0c568ed2435da625b3e40bc133c46<a0> (tuple_proj<a0>.0 self_) x)";
        true
    }

    fn g(&self, x: i64) -> i64 {
        x
    }

    fn f(&self, x: i64) -> i64 {
        self.inner.g(x)
    }
}

fn main() {}
