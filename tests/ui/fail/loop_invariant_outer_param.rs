//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

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
        thrust_macros::invariant!(|a: i64, v: i64| true);
        v = a;
    }

    v
}

fn main() {}
