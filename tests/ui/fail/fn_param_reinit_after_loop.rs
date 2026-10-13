//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct S {
    x: i64,
}

impl thrust_models::Model for S {
    type Ty = Self;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> bool {
    unimplemented!()
}

fn id(x: i64) -> i64 {
    x
}

#[thrust_macros::ensures(result == a.x + 1)]
#[thrust_macros::context]
fn keep_argument(mut a: S) -> i64 {
    let mut v = a.x;
    while rand() {
        thrust_macros::invariant!(|a: S, v: i64| v == a.x);
        v = a.x;
    }
    let t = a;
    a = S { x: id(t.x) };
    let _ = a.x;
    v
}

fn main() {}
