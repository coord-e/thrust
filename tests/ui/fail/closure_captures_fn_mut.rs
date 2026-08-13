//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

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
    assert!(r == 5);
}
