//@check-pass
//@compile-flags: -C debug-assertions=off

#[thrust::trusted]
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.1 >= 2)]
fn two_elem_slice() -> &'static [i32] {
    unimplemented!()
}

fn main() {
    let s = two_elem_slice();
    let _ = s[0];
    let _ = s[1];
}
