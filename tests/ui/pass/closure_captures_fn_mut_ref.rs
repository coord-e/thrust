//@check-pass
//@compile-flags: -C debug-assertions=off

// A `FnMut` closure that captures by mutable borrow carries two `Mut` levels: the outer
// one is the environment's, holding the slot on entry (`*acc`) and on exit (`!acc`),
// and the inner one is the borrow's, whose current value is what the counter holds. So
// counting up by one across the call reads `*(!acc) == *(*acc) + 1`.
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
