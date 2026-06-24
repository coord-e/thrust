//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.len() > 0)]
fn nonempty_slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let s = nonempty_slice();
    assert!(s.len() > 0);
    let _ = s[0];
}
