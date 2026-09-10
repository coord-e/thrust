//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::Seq;
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

struct Run<I: Iterator + Model>
where
    I::Item: Model,
{
    iter: I,
    items: Ghost<Seq<<I::Item as Model>::Ty>>,
}

impl<I: Iterator + Model> Model for Run<I>
where
    I::Item: Model,
{
    type Ty = (<I as Model>::Ty, Seq<<I::Item as Model>::Ty>);
}

// A fold whose accumulator is related to the produced history by the returned value.
#[thrust_macros::context]
#[thrust_macros::requires(I::invariant((*r).0))]
#[thrust_macros::ensures(result == (!r).1.len())]
fn count<I: Iterator + Model>(r: &mut Run<I>) -> i64
where
    I::Item: Model,
    <I as Model>::Ty: PartialEq,
    <I::Item as Model>::Ty: PartialEq,
{
    let rr = r;
    let mut acc = 0;
    while let Some(x) = rr.iter.next() {
        thrust_macros::invariant!(
            |rr: &mut Run<I>, r: thrust_models::FnParam<&mut Run<I>>, acc: i64|
            I::invariant((*rr).0) && !rr == !r.at_entry() && acc == (*rr).1.len()
        );
        rr.items = thrust_macros::ghost!(
            |rr: &mut Run<I>, x: I::Item| -> Seq<<I::Item as Model>::Ty> { (*rr).1.push(x) }
        );
        acc += 1;
    }
    acc
}

fn main() {}
