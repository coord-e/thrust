//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct Counter;

fn use_counter(c: Counter) -> Counter {
    let _x: Counter = c;
    _x
}

fn main() {
    let c = Counter;
    let _ = use_counter(c);
    assert!(false);
}
