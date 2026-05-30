//@check-pass
//@compile-flags: -C debug-assertions=off

// Multiple `invariant!` calls at the same loop header are AND'd: the proof
// below needs both `x >= 1` and `y >= 1` to be carried across the back edge.

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

fn main() {
    let mut x = 1_i64;
    let mut y = 1_i64;
    while rand() == 0 {
        thrust_macros::invariant!(|x: i64| x >= 1);
        thrust_macros::invariant!(|y: i64| y >= 1);
        let t1 = x;
        let t2 = y;
        x = t1 + t2;
        y = t1 + t2;
    }
    assert!(x >= 1 && y >= 1);
}
