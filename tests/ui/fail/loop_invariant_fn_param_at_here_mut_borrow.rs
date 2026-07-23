//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// `a` is mutably borrowed and incremented through the borrow, so its current value (`at_here`)
// diverges from its entry value. Claiming `is_not_changed()` (i.e. `at_entry() == at_here()`) is
// therefore not inductive: it holds on entry but is broken by `*r += 1`, so verification fails.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

#[thrust_macros::ensures(result == a)]
#[thrust_macros::invariant_context]
fn count_up(mut a: i64) -> i64 {
    while rand() {
        thrust_macros::invariant!(|a: thrust_models::FnParam<i64>| a.is_not_changed());
        let r = &mut a;
        *r += 1;
    }

    a
}

fn main() {}
