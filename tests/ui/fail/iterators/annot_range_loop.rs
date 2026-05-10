//@error-in-other-file: Unsat
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

    let mut count = 0;
    while let Some(i) = range.next() {
        count += 1;
    }

    assert!(range.start != count);
}
