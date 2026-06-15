//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// Same shape as the `pass` counterpart, but the invariant asserts the predicate
// `Self::step(c, it, c)` outright. `step` relates a state to its *successor*
// (`dist.start == self.start + 1`), so it can never hold with `dist == c`: the
// invariant is not inductive and verification fails with `Unsat`.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 {
    unimplemented!()
}

#[thrust_macros::context]
trait Foo {
    type Item;

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool;

    #[thrust_macros::invariant_context]
    fn run(self, item: Self::Item)
    where
        Self: Sized,
    {
        let c = self;
        let it = item;
        while rand() == 0 {
            thrust_macros::invariant!(|c: Self, it: Self::Item| Self::step(c, it, c));
        }
        let _last = c;
        let _last_item = it;
    }
}

#[derive(PartialEq)]
struct Range {
    start: i64,
    end: i64,
}

impl thrust_models::Model for Range {
    type Ty = Range;
}

#[thrust_macros::context]
impl Foo for Range {
    type Item = i64;

    #[thrust_macros::predicate]
    fn step(self, item: Self::Item, dist: Self) -> bool {
        // self.end == dist.end && self.start == item && self.start + 1 == dist.start
        "(and
            (= (tuple_proj<Int-Int>.1 self_) (tuple_proj<Int-Int>.1 dist))
            (= (tuple_proj<Int-Int>.0 self_) item)
            (= (+ (tuple_proj<Int-Int>.0 self_) 1) (tuple_proj<Int-Int>.0 dist))
        )";
        true
    }
}

fn main() {
    Range { start: 0, end: 5 }.run(0);
}
