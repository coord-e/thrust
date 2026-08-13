//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// The captured `acc` counts up from 0, so the first call returns 4.
fn main() {
    let mut acc = 0;
    let mut f = thrust_macros::closure!(
        captures(acc: &mut i32),
        ensures(result == x + 1 && !acc == *acc + 1),
        move |x: i32| -> i32 {
            acc += 1;
            x + acc
        },
    );
    let r = f(3);
    assert!(r == 5);
}
