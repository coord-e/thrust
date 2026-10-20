//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off -C opt-level=3

#[thrust::trusted]
#[thrust_macros::requires(x != 0)]
#[thrust_macros::ensures(true)]
fn assume_nonzero(x: i32) {}

fn main() {
    assume_nonzero(0);
}
