//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

use thrust_models::exists;

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::ensures(
        Self::completed(*self)
        || exists(|i| (result == Some(i)) && Self::step(*self, i, !self))
    )]
    #[thrust_macros::ensures(!Self::completed(*self) || (result == None && *self == !self))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn completed(self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;

    #[thrust_macros::invariant_context]
    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(
        exists(|it: thrust_models::model::Vec<Self>|
        exists(|fn_: thrust_models::model::Vec<F>|
        exists(|acc|
        exists(|l: thrust_models::model::Int|
            it.0[0] == self &&
            acc.0[0] == init &&
            Self::completed(it.0[l - 1]) &&
            result == acc.0[l - 1] &&
            l > 0 &&
            !(
                exists(|i|
                    (0 <= i && i < l - 1) &&
                    !(
                        exists(|item|
                            !Self::completed(it.0[i]) &&
                            Self::step(it.0[i], item, it.0[i + 1]) &&
                            thrust_macros::pre!(f(acc.0[i], item)) &&
                            thrust_macros::post!(
                                f(acc.0[i], item),
                                acc.0[i + 1]
                            )
                        )
                    )
                )
            )
        ))))
    )]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
            thrust_macros::invariant!(
                |accum: B|
                exists(|it: thrust_models::model::Vec<Self>|
                exists(|fn_: thrust_models::model::Vec<F>|
                exists(|acc|
                exists(|l: thrust_models::model::Int|
                    it.0[0] == self &&
                    fn_.0[0] == f &&
                    acc.0[0] == init &&
                    accum == acc.0[l - 1] &&
                    l > 0 &&
                    !(
                        exists(|i: thrust_models::model::Int|
                            (0 <= i && i < l - 1) &&
                            !(
                                exists(|item: Self::Item|
                                    !Self::completed(it.0[i]) &&
                                    Self::step(it.0[i], item, it.0[i + 1]) &&
                                    thrust_macros::pre!(f(acc.0[i], item)) &&
                                    thrust_macros::post!(
                                        f(acc.0[i], item),
                                        acc.0[i + 1]
                                    )
                                )
                            )
                        )
                    )
                ))))
            );
            accum = f(accum, x);
        }
        accum
    }
}

struct Range {
    start: i64,
    end: i64,
}

impl thrust_models::Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Iterator for Range {
    type Item = i64;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start < self.end {
            let item = self.start;
            self.start += 1;
            Some(item)
        } else {
            None
        }
    }

    #[thrust_macros::predicate]
    fn completed(self) -> bool {
        // (tuple_proj<Int-Int>.0 self) is equivalent to self.start
        // !(self.start < self.end) is written as following:
        "(not (<
            (tuple_proj<Int-Int>.0 self_)
            (tuple_proj<Int-Int>.1 self_)
        ))";
        true
    }

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.end == dist.end && self.start == item && self.start + 1 == dist.start
        // is written as following:
        "(and
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }
}

fn main() {
    let mut range = Range { start: 0, end: 5 };
    let sum = range.fold(0, |x, y| x + y);

    assert!(sum == 10);
}