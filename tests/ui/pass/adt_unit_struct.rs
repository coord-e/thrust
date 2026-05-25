//@check-pass
//@compile-flags: -C debug-assertions=off

struct Counter;

fn use_counter(c: Counter) -> Counter {
    let _x: Counter = c;
    _x
}

fn take_token(mut t: Counter) -> Counter {
    t = Counter;
    t
}

fn main() {
    let c = Counter;
    let _ = use_counter(c);
    let _ = take_token(Counter);
}
