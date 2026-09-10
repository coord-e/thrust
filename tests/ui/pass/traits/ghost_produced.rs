//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::{Ghost, Model};

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::requires(Self::invariant(*self))]
    #[thrust_macros::ensures(Self::invariant(!self))]
    #[thrust_macros::ensures(result == None ==> Self::completed(self))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::step(*self, i, !self)))]
    #[thrust_macros::ensures(forall(|i| result == Some(i) ==> Self::item_ok(i)))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
    #[thrust_macros::predicate]
    fn item_ok(item: Self::Item) -> bool;
}

// The history of produced items lives in a ghost field, updated by the loop body,
// so the specification never has to existentially quantify it.
struct Run<I: Iterator>
where
    I::Item: Model,
{
    iter: I,
    produced: Ghost<Seq<<I::Item as Model>::Ty>>,
}

impl<I: Iterator + Model> Model for Run<I>
where
    I::Item: Model,
{
    type Ty = (<I as Model>::Ty, Seq<<I::Item as Model>::Ty>);
}

#[thrust_macros::context]
#[thrust_macros::requires(I::invariant((*r).0) && (*r).1.len() == 0)]
#[thrust_macros::ensures(
    forall(|k: Int| 0 <= k && k < (!r).1.len() ==> I::item_ok((!r).1[k]))
)]
fn drain<I: Iterator + Model>(r: &mut Run<I>)
where
    I::Item: Model,
    <I as Model>::Ty: PartialEq,
    <I::Item as Model>::Ty: PartialEq,
{
    let rr = r;
    while let Some(x) = rr.iter.next() {
        thrust_macros::invariant!(
            |rr: &mut Run<I>, r: thrust_models::FnParam<&mut Run<I>>|
            I::invariant((*rr).0)
                && !rr == !r.at_entry()
                && forall(|k: Int| 0 <= k && k < (*rr).1.len() ==> I::item_ok((*rr).1[k]))
        );
        rr.produced = thrust_macros::ghost!(
            |rr: &mut Run<I>, x: I::Item| -> Seq<<I::Item as Model>::Ty> { (*rr).1.push(x) }
        );
    }
}

fn main() {}
