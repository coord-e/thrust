//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

#[thrust_macros::context]
trait A {
    type Item;

    #[thrust_macros::ensures(thrust_models::forall(|i| result == Some(i) ==> Self::ok(*self, i)))]
    fn get(&mut self) -> Option<Self::Item>;

    fn other(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn ok(self, i: Self::Item) -> bool;
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
    <I as A>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn ok(self, i: Self::Item) -> bool {
        // I::ok(self.inner, i)
        "(q_ok_200bb7d187270ed1be2cc56b0bc48aad<a0> (tuple_proj<a0>.0 self_) i)";
        true
    }

    fn other(&mut self) -> Option<Self::Item> {
        self.inner.other()
    }

    fn get(&mut self) -> Option<Self::Item> {
        match self.inner.get() {
            Some(v) => Some(v),
            None => None,
        }
    }
}

fn main() {}
