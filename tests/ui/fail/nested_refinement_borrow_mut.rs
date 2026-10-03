//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: &mut { b: Box<i32> | *b >= 0 })]
fn overwrite(x: &mut Box<i32>) {
    **x = -1;
}

fn main() {}
