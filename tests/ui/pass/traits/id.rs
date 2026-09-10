//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
use thrust_models::forall;

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

pub struct Id<I> {
    iter: I,
}

impl<I> thrust_models::Model for Id<I> {
    type Ty = Id<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Id<I>
where
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.iter.invariant()
        "(q_invariant_c7a091bc1d03c6cf87779283240d85c2<a0> (tuple_proj<a0>.0 self_))";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // self.iter.completed()
        "(and
            (q_completed_c7a091bc1d03c6cfc9dcf35ce8b9e5a<a0>
                (mut<a0>
                    (tuple_proj<a0>.0 (mut_current<Tuple<a0>> self_))
                    (tuple_proj<a0>.0 (mut_final<Tuple<a0>> self_))
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist.iter)
        "(q_step_c7a091bc1d03c6cfc09f2d4a4c0c07ff<a0>
            (tuple_proj<a0>.0 self_)
            item
            (tuple_proj<a0>.0 dist)
        )";
        true
    }

    fn next(&mut self) -> Option<I::Item> {
        self.iter.next()
    }
}

fn main() {}
