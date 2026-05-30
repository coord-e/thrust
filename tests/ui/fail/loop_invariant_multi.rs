//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Both invariants are AND'd. If either is too weak to be inductive, the
// verification fails — here `y >= 2` does not hold initially.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
    let mut x = 1_i64;
    let mut y = 1_i64;
    while rand() == 0 {
        thrust_macros::invariant!(|x: i64| x >= 1);
        thrust_macros::invariant!(|y: i64| y >= 2);
        let t1 = x;
        let t2 = y;
        x = t1 + t2;
        y = t1 + t2;
    }
    assert!(x >= 1 && y >= 2);
}
