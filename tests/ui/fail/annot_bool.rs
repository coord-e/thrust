//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(b)]
#[thrust_macros::ensures(result == 1)]
fn one_if(b: bool) -> i64 {
    if b {
        1
    } else {
        0
    }
}

#[thrust_macros::requires(!b)]
#[thrust_macros::ensures(result == 0)]
fn zero_unless(b: bool) -> i64 {
    if b {
        1
    } else {
        0
    }
}

#[thrust_macros::requires(b && c)]
#[thrust_macros::ensures(result == 2)]
fn both(b: bool, c: bool) -> i64 {
    let mut n = 0;
    if b {
        n += 1;
    }
    if c {
        n += 1;
    }
    n
}

#[thrust_macros::requires(b ==> c)]
#[thrust_macros::ensures(result == 0)]
fn not_only_first(b: bool, c: bool) -> i64 {
    if b && !c {
        1
    } else {
        0
    }
}

#[thrust_macros::requires(x > 0)]
#[thrust_macros::ensures(result)]
fn pos(x: i64) -> bool {
    x > 1
}

fn main() {
    assert!(one_if(true) == 1);
    assert!(zero_unless(false) == 0);
    assert!(both(true, true) == 2);
    assert!(not_only_first(true, true) == 0);
    assert!(pos(1));
}
