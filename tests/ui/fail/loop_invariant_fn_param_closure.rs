//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// A loop invariant refers to a closure parameter via `FnParam<F>`, whose
// `f.at_entry()` yields `Closure<F>`. Here the invariant relates `acc` to the
// entry closure's postcondition, from which the postcondition below is proven.
#[thrust_macros::ensures((n > 0) ==> thrust_macros::post!(f(n - 1), result))]
#[thrust_macros::invariant_context]
fn last_apply<F>(f: F, n: i64) -> i64
where
    F: Fn(i64) -> i64,
{
    let mut acc = 0_i64;
    let mut i = 0_i64;
    while i < n {
        thrust_macros::invariant!(
            |i: i64, acc: i64, f: thrust_models::FnParam<F>|
            (i > 0) ==> thrust_macros::post!(f.at_entry()(i - 1), acc)
        );
        acc = f(i);
        i += 1;
    }
    acc
}

// A capture-free closure is null (singleton) sorted; comparing its identity
// must collapse to a canonical value rather than ICE during clause building.
#[thrust_macros::invariant_context]
fn unchanged<F>(mut f: F)
where
    F: FnMut(i64) -> i64,
{
    let _ = &mut f;
    let mut i = 0_i64;
    while i < 10 {
        thrust_macros::invariant!(
            |i: i64, f: thrust_models::FnParam<F>|
            f.at_entry() == f.at_entry() && i <= 10
        );
        i += 1;
    }
    assert!(i == 11); // Unsat: the loop exits with i == 10
}

fn main() {
    let c = 7_i64;
    let _ = last_apply(|x| x + c, 10);

    unchanged(|x| x + 1);
}
