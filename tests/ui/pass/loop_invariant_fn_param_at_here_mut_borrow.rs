//@check-pass
//@compile-flags: -C debug-assertions=off

// `a` is mutably borrowed in the loop body, making it flow-bound; its current value (`at_here`)
// then genuinely differs from its value at function entry (`at_entry`). `a` only grows, so the
// invariant `a.at_entry() <= a.at_here()` is inductive and discharges `result >= a` (entry value).

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

#[thrust_macros::ensures(result >= a)]
#[thrust_macros::invariant_context]
fn count_up(mut a: i64) -> i64 {
    while rand() {
        thrust_macros::invariant!(|a: thrust_models::FnParam<i64>| a.at_entry() <= a.at_here());
        let r = &mut a;
        *r += 1;
    }

    a
}

fn main() {}
