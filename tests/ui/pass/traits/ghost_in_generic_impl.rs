//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::model::Int;
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
trait A {
    type Item;

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(true)]
    fn f(&mut self);
}

#[thrust_macros::requires(g == 1)]
fn expect_one(g: Ghost<Int>) {
    let _ = g;
}

struct W<I> {
    inner: I,
}

impl<I> Model for W<I> {
    type Ty = W<I>;
}

// The trait declares an associated type, so the formula lifted out of `ghost!`
// carries a `Self::Item: Model` bound. `Self` reaches the lifted function as the
// impl's self type, where the projection needs the trait to stay unambiguous.
#[thrust_macros::context]
impl<I> A for W<I>
where
    I: A + Model,
    <I as A>::Item: Model,
    <<I as A>::Item as Model>::Ty: PartialEq,
    <I as Model>::Ty: PartialEq,
{
    type Item = I::Item;

    fn f(&mut self) {
        let one: i64 = 1;
        let g = thrust_macros::ghost!(|one: i64| -> Int { one });
        expect_one(g);
        self.inner.f();
    }
}

fn main() {}
