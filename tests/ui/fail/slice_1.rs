//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.1 == 0)]
fn empty_slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let s = empty_slice();
    let _ = s[0];
}
