//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::requires(true)]
#[thrust::ensures(^x == ((*x).1, (*x).1))]
fn swap_tuple(x: &mut (i32, i32)) {
    let v = *x;
    *x = (v.1, v.0);
}

fn main() {}
