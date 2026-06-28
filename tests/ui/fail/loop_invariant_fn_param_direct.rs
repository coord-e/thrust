//@error-in-other-file: refers to function parameter `a` directly
//@compile-flags: -C debug-assertions=off

// Referring to a function argument's local directly (without `FnParam`) is rejected: the choice
// between its entry value and its current value must be made explicit via `FnParam` and
// `at_entry()`/`at_here()`.

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
        thrust_macros::invariant!(|a: i64, v: i64| v == a);
        v = a;
    }

    v
}

fn main() {}
