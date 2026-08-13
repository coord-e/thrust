//@check-pass
//@compile-flags: -C debug-assertions=off

// A `FnMut` closure receives its environment as a `Mut`, so every capture carries both
// the value on entry (`*acc`) and the value on exit (`!acc`), and is restated one `&mut`
// deeper than what it is captured as. The body has to prove the relation between the
// two, which is what pins the environment down.
//
// The closure is called directly: reaching it through `pre!`/`post!` instead would hand
// the specification an environment without that `Mut`.
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
    assert!(r == 4);
}
