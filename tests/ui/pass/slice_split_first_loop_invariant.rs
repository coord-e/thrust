//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(slice: &[i32]) {
    let mut s = slice;
    let mut i = 0;
    while i < slice.len() {
        thrust_macros::invariant!(|slice: &[i32], s: &[i32], i: usize| 0 <= i
            && i <= (*slice).len()
            && *s == (*slice).subsequence(i, (*slice).len()));
        if let Some((first, rest)) = s.split_first() {
            assert!(*first == slice[i]);
            s = rest;
            i += 1;
        } else {
            break;
        }
    }
}

fn main() {}
