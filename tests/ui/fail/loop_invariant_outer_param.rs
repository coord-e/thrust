//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Without `is_not_changed()` the invariant only relates `v` to the argument's *current* local
// (`at_here`); nothing ties that back to the entry value, so the `result == a` postcondition (whose
// `a` is the entry value) cannot be discharged.

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
        thrust_macros::invariant!(|a: thrust_models::FnParam<i64>, v: i64| v == a.at_here());
        v = a;
    }

    v
}

fn main() {}
