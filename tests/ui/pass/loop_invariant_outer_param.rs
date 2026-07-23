//@check-pass
//@compile-flags: -C debug-assertions=off

// A user-supplied loop invariant replaces the inferred precondition, so it must itself relate the
// argument's value at function entry (`at_entry`, the `OuterFnParam`) to its current local
// (`at_here`). Here `a` is never reassigned, so `is_not_changed()` ties the two together and lets
// `v == a.at_here()` discharge the `result == a` postcondition (whose `a` is the entry value).

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
            |a: thrust_models::FnParam<i64>, v: i64| a.is_not_changed() && v == a.at_here()
        );
        v = a;
    }

    v
}

fn main() {}
