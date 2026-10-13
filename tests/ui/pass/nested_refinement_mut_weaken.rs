//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
#[thrust_macros::ret(&mut { v: i32 | v >= 0 })]
fn weaken(x: &mut i32) -> &mut i32 {
    x
}

fn main() {}
