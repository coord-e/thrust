//@check-pass
//@compile-flags: -C debug-assertions=off -A unused-variables

use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

struct Counter {
    count: i64,
    seen: Ghost<Seq<Int>>,
}

impl thrust_models::Model for Counter {
    type Ty = (Int, Seq<Int>);
}

#[thrust_macros::context]
impl Counter {
    #[thrust_macros::requires((*self).1.len() == (*self).0)]
    #[thrust_macros::ensures((!self).1.len() == (!self).0)]
    fn record(&mut self, x: i64) {
        self.count += 1;
        self.seen =
            thrust_macros::ghost!(|self: &mut Self, x: i64| -> Seq<Int> { (*self).1.push(x) });
    }
}

fn main() {}
