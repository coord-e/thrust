//@check-pass
//@compile-flags: -C debug-assertions=off

struct Counter;
struct Token;

fn use_counter(c: Counter) -> Counter {
    let _x: Counter = c;
    _x
}

fn take_token(mut t: Token) -> Token {
    t = Token;
    t
}

fn main() {
    let c = Counter;
    let _ = use_counter(c);
    let _ = take_token(Token);
}
