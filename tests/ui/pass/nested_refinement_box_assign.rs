//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::param(x: Box<{ v: i32 | v >= 0 }>)]
fn overwrite(mut x: Box<i32>) {
    *x = 1;
}

fn main() {}
