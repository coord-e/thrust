//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: Box<{ b: Box<i32> | *b >= 0 }>)]
fn overwrite(mut x: Box<Box<i32>>) {
    **x = -1;
}

fn main() {}
