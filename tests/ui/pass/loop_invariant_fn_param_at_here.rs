//@check-pass
//@compile-flags: -C debug-assertions=off

// When the argument is mutable and mutated in the loop body, `at_here()` (its current value)
// genuinely differs from `at_entry()` (its value at function entry). `a` only grows, so the
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
        a += 1;
    }

    a
}

fn main() {}
