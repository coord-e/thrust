//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
#[thrust_macros::ret(&mut { v: i32 | v >= 0 })]
fn identity(x: &mut i32) -> &mut i32 {
    x
}

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
#[thrust_macros::ret(&mut { v: i32 | v >= 0 })]
fn reborrow(x: &mut i32) -> &mut i32 {
    *x = 1;
    identity(x)
}

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
fn update(x: &mut i32) {
    *reborrow(x) = 2;
    assert!(*x >= 0);
}

fn main() {}
