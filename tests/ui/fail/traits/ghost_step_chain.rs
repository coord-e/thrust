//@error-in-other-file: Unsat
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
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool;
    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;
}

// The state and item histories that fold's specification used to quantify
// existentially now live in ghost fields the loop body maintains.
struct Run<I: Iterator + Model>
where
    I::Item: Model,
{
    iter: I,
    states: Ghost<Seq<<I as Model>::Ty>>,
    items: Ghost<Seq<<I::Item as Model>::Ty>>,
}

impl<I: Iterator + Model> Model for Run<I>
where
    I::Item: Model,
{
    type Ty = (<I as Model>::Ty, Seq<<I as Model>::Ty>, Seq<<I::Item as Model>::Ty>);
}

#[thrust_macros::context]
#[thrust_macros::requires(
    I::invariant((*r).0) && (*r).1.len() == 1 && (*r).1[0] == (*r).0
)]
#[thrust_macros::ensures(
    forall(|k: Int| 0 <= k && k < (!r).2.len() ==> I::step((!r).1[k], (!r).2[k], (!r).1[k + 1]))
)]
fn drain_chain<I: Iterator + Model>(r: &mut Run<I>)
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
                && (*rr).1.len() == (*rr).2.len() + 1
                && (*rr).1[(*rr).2.len()] == (*rr).0
                && forall(|k: Int|
                    0 <= k && k < (*rr).2.len()
                    ==> I::step((*rr).1[k], (*rr).2[k], (*rr).1[k + 1])
                )
        );
        rr.items = thrust_macros::ghost!(
            |rr: &mut Run<I>, x: I::Item| -> Seq<<I::Item as Model>::Ty> { (*rr).2.push(x) }
        );
        rr.states = thrust_macros::ghost!(
            |rr: &mut Run<I>| -> Seq<<I as Model>::Ty> { (*rr).1.push((*rr).0) }
        );
    }
}

fn main() {}
