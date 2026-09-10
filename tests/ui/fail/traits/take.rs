//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest
//@compile-flags: -C debug-assertions=off
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

pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I> thrust_models::Model for Take<I> {
    type Ty = Take<I>;
}

#[thrust_macros::context]
impl<I> Iterator for Take<I>
where
    I: Iterator + thrust_models::Model,
    <I as Iterator>::Item: thrust_models::Model,
    <I as thrust_models::Model>::Ty: PartialEq,
{
    type Item = I::Item;

    #[thrust_macros::predicate]
    fn invariant(self) -> bool {
        // self.invariant() && self.n >= 0
        "(and
            (q_invariant_8cab213534b4e34b5a37430c4d78e732<a0> (tuple_proj<a0-Int>.0 self_))
            (>= (tuple_proj<a0-Int>.1 self_) 0)
        )";
        true
    }

    #[thrust_macros::predicate]
    fn completed(&mut self) -> bool {
        // (*self.n == 0 && *self.iter == !self.iter && *self.n == !self.n) ||
        // (*self.iter.completed() && *self.n - 1 == !self.n)
        "(or
            (and
                (= (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 0)
                (=
                    (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                    (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))
                )
                (=
                    (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_))
                    (tuple_proj<a0-Int>.1 (mut_final<Tuple<a0-Int>> self_))
                )
            )
            (and
                (q_completed_8cab213534b4e34b784965d8b6f1934e<a0>
                    (mut<a0>
                        (tuple_proj<a0-Int>.0 (mut_current<Tuple<a0-Int>> self_))
                        (tuple_proj<a0-Int>.0 (mut_final<Tuple<a0-Int>> self_))
                    )
                )
                (=
                    (- (tuple_proj<a0-Int>.1 (mut_current<Tuple<a0-Int>> self_)) 1)
                    (tuple_proj<a0-Int>.1 (mut_final<Tuple<a0-Int>> self_))
                )
            )
        )";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.iter.step(item, dist.iter) && dist.n == self.n - 1
        "(and
            (q_step_8cab213534b4e34bf21e5845fb0de6dd<a0>
                (tuple_proj<a0-Int>.0 self_)
                item
                (tuple_proj<a0-Int>.0 dist)
            )
            (= 
                (tuple_proj<a0-Int>.1 dist)
                (- (tuple_proj<a0-Int>.1 self_) 1)
            )
        )";
        true
    }

    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 2;
            self.iter.next()
        } else {
            None
        }
    }
}

fn main() {}
