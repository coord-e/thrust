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

#[thrust_macros::requires((*c).1.len() == (*c).0)]
#[thrust_macros::ensures((!c).1.len() == (!c).0)]
fn record(c: &mut Counter, x: i64) {
    c.count += 1;
    c.seen = thrust_macros::ghost!(|c: &mut Counter, x: i64| -> Seq<Int> { (*c).1.push(x) });
}

fn main() {}
