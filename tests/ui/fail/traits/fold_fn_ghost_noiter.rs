//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -A unused-variables
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper THRUST_SOLVER_TIMEOUT_SECS=60 COAR_IMAGE=coar:latest

use thrust_models::forall;
use thrust_models::model::{Int, Seq};
use thrust_models::Ghost;

struct Run {
    items: Ghost<Seq<Int>>,
    accs: Ghost<Seq<Int>>,
}

impl thrust_models::Model for Run {
    type Ty = (Seq<Int>, Seq<Int>);
}

// `Fn` rather than `FnMut`: the closure has no state to project, so the accumulator
// chain needs no prophecy, only the closure's own pre/postcondition.
#[thrust_macros::context]
#[thrust_macros::requires(
    n >= 0
        && (*r).0.len() == 0
        && (*r).1.len() == 1
        && forall(|a: Int| forall(|x: Int| thrust_macros::pre!(f(a, x))))
)]
#[thrust_macros::ensures(
    result == (!r).1[(!r).0.len()]
        && (!r).1.len() == (!r).0.len() + 1
        && forall(|k: Int|
            0 <= k && k < (!r).0.len()
                ==> thrust_macros::post!(f((!r).1[k], (!r).0[k]), (!r).1[k + 1])
        )
)]
fn fold_upto<F: Fn(i64, i64) -> i64>(r: &mut Run, n: i64, init: i64, f: F) -> i64 {
    let rr = r;
    let mut acc = init;
    let mut i = 0;
    while i < n {
        thrust_macros::invariant!(
            |rr: &mut Run, r: thrust_models::FnParam<&mut Run>, f: F, acc: i64, i: i64, n: i64|
            0 <= i && i <= n
                && !rr == !r.at_entry()
                && (*rr).0.len() == i
                && (*rr).1.len() == (*rr).0.len() + 1
                && acc == (*rr).1[(*rr).0.len()]
                && forall(|a: Int| forall(|x: Int| thrust_macros::pre!(f(a, x))))
                && forall(|k: Int|
                    0 <= k && k < (*rr).0.len()
                        ==> thrust_macros::post!(f((*rr).1[k], (*rr).0[k]), (*rr).1[k + 1])
                )
        );
        acc = f(acc, i);
        rr.items = thrust_macros::ghost!(|rr: &mut Run, i: i64| -> Seq<Int> { (*rr).0.push(i) });
        rr.accs = thrust_macros::ghost!(|rr: &mut Run, acc: i64| -> Seq<Int> { (*rr).1.push(acc) });
        i += 1;
    }
    acc
}

fn main() {}
