//@check-pass
//@compile-flags: -C debug-assertions=off

// The paired pass for `fail/loop_invariant_fn_param_direct`: the same program with the function
// argument referred to explicitly via `FnParam`. `is_not_changed()` ties the entry and current
// views together, so `v == a.at_entry()` discharges the `result == a` postcondition.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

#[thrust_macros::ensures(result == a)]
#[thrust_macros::invariant_context]
fn keep_argument(a: i64) -> i64 {
    let mut v = a;

    while rand() {
        thrust_macros::invariant!(
            |a: thrust_models::FnParam<i64>, v: i64| a.is_not_changed() && v == a.at_entry()
        );
        v = a;
    }

    v
}

fn main() {}
