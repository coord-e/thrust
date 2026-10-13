//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { v: i32 | v >= 0 })]
fn overwrite(x: &mut i32) {
    *x = -1;
}

fn main() {}
