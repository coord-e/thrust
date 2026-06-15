//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60

// A loop invariant in a *trait default method* may refer to `Self`, the trait's
// associated types (`Self::Item`) and its predicates (`Self::step`). The
// invariant is rewritten into a free `formula_fn` in which `Self` becomes a
// synthetic generic, so that generic must inherit the host `Self: Foo` bound for
// the associated type / predicate to remain resolvable.

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
            thrust_macros::invariant!(|c: Self, it: Self::Item| Self::step(c, it, c) || true);
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
