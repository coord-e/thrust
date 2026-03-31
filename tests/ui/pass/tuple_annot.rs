//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(!x == ((*x).1, (*x).0))]
fn swap_tuple(x: &mut (i32, i32)) {
    let v = *x;
    *x = (v.1, v.0);
}

fn main() {}
