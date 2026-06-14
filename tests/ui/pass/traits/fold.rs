//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

#[thrust_macros::context]
trait Iterator {
    type Item;

    #[thrust_macros::ensures(
        Self::completed(*self)
        || thrust_models::exists(|i| (result == Some(i)) && Self::step(*self, i, !self))
    )]
    #[thrust_macros::ensures(!Self::completed(*self) || (result == None && *self == !self))]
    fn next(&mut self) -> Option<Self::Item>;

    #[thrust_macros::predicate]
    fn completed(self) -> bool;
    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;

    #[thrust_macros::requires(true)]
    #[thrust_macros::ensures(
        // ∃ it: Vec<Self>.   (it.0 : Array<Int, Self>, it.1 : Int)
        thrust_models::exists(|it: thrust_models::model::Vec<Self>|
        // ∃ acc: Vec<B>.     (acc.0 : Array<Int, B>,   acc.1 : Int)
        thrust_models::exists(|acc|
            it.0[0] == *self &&
            acc.0[0] == init &&
            Self::completed(it.0[it.1 - 1]) &&
            result == acc.0[it.1 - 1] &&
            // ∀ i. (0 ≤ i ∧ i < it.1 - 1) ⟹
            //   ∃ item. Self::step(it[i], item, it[i+1])
            //     ∧ post!(f(acc[i], item), acc[i+1])
            //        !(∃ i. (0 ≤ i ∧ i < it.1 - 1) ∧ !(∃ item. step ∧ post))
            !(
                thrust_models::exists(|i|
                    (0 <= i && i < it.1 - 1) &&
                    !(
                        thrust_models::exists(|item|
                            Self::step(it.0[i], item, it.0[i + 1]) &&
                            thrust_macros::post!(
                                f(acc.0[i], item),
                                acc.0[i + 1]
                            )
                        )
                    )
                )
            )
        ))
    )]
    fn fold<B, F>(mut self, init: B, mut f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        let mut accum = init;
        while let Some(x) = self.next() {
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