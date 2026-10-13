//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
#[thrust_macros::ret(&mut { v: i32 | v >= 0 })]
fn identity(x: &mut i32) -> &mut i32 {
    x
}

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
fn update(x: &mut i32) {
    let y = identity(x);
    let mut n = 0;
    while n < 2 {
        *y = n;
        n += 1;
    }
    *y = -1;
}

fn main() {}
