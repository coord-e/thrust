//@error-in-other-file: Unsat
//@compile-flags: -Adead_code -C debug-assertions=off

#[derive(PartialEq)]
struct P {
    x: i64,
    y: i64,
}

impl thrust_models::Model for P {
    type Ty = Self;
}

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.x == p.x && result.y == p.y)]
fn swap(p: P) -> P {
    P { x: p.y, y: p.x }
}

fn main() {
    let p = P { x: 3, y: 5 };
    let q = swap(p);
    assert!(q.x == 5 && q.y == 3);
}
