//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

struct Wrap {
    o: Option<i32>,
    n: i32,
}

fn get_n(w: Wrap) -> i32 {
    w.n
}

// No local here has a type mentioning `Option`: the enum is reachable only as a
// field type of `Wrap`, and only the drop of `w` in `get_n` needs its definition.
#[thrust::callable]
fn check(w: Wrap) {
    let n = w.n;
    assert!(get_n(w) == n + 1);
}

fn main() {}
