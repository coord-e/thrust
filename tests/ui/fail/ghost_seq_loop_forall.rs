//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

struct Recorder {
    count: i64,
    hist: Ghost<Seq<Int>>,
}

impl thrust_models::Model for Recorder {
    type Ty = (Int, Seq<Int>);
}

#[thrust_macros::context]
#[thrust_macros::requires((*r).0 == 0 && (*r).1.len() == 0 && n >= 0)]
#[thrust_macros::ensures(forall(|k: Int| 0 <= k && k < (!r).1.len() ==> (!r).1[k] < n))]
fn record_bounded(r: &mut Recorder, n: i64) {
    let rr = r;
    let mut i = 0;
    while i < n {
        thrust_macros::invariant!(
            |rr: &mut Recorder, r: thrust_models::FnParam<&mut Recorder>, i: i64, n: i64|
            0 <= i && i <= n && (*rr).1.len() == i && !rr == !r.at_entry()
        );
        rr.hist = thrust_macros::ghost!(|rr: &mut Recorder, i: i64| -> Seq<Int> { (*rr).1.push(i) });
        rr.count += 1;
        i += 1;
    }
}

fn main() {}
