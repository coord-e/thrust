//@check-pass
//@compile-flags: -C debug-assertions=off

// A `FnMut` environment is itself a `Mut`, so a mutable-borrow capture has two levels:
// the outer holds the slot on entry (`*acc`) and on exit (`!acc`), the inner is the
// borrow, whose current value is the counter. Hence `*(!acc)`, not `!(*acc)`.
fn main() {
    let mut acc = 0;
    let mut f = thrust_macros::closure!(
        captures(acc: &mut &mut i32),
        ensures(result == x + 1 && *(!acc) == *(*acc) + 1),
        |x: i32| -> i32 {
            acc += 1;
            x + acc
        },
    );
    let r = f(3);
    assert!(r == 4);
}
