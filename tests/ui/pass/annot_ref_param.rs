//@check-pass
//@compile-flags: -Adead_code -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
fn increment(x: &mut i32) {
    *x += 1;
}

fn main() {
    let mut a = 0;
    increment(&mut a);
}
