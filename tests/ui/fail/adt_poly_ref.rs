//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

enum X<'a, T> {
    A(&'a T),
}

fn main() {
    let i = 42;
    let x = X::A(&i);
    match x {
        X::A(i) => assert!(*i == 41),
    }
}
