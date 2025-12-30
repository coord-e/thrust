//@error-in-other-file: Unsat

#[thrust::extern_spec_fn]
#[thrust::requires(true)]
#[thrust::ensures(result == *dest && ^dest == 0)]
fn _extern_spec_take(dest: &mut i32) -> i32 {
    std::mem::take(dest)
}

fn main() {
    let mut x = 42;
    let old = std::mem::take(&mut x);
    assert!(x == 42);
}
