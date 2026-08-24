//@check-pass
//@compile-flags: -C debug-assertions=off -C opt-level=2

// At `-C opt-level=1` and above rustc reads slice metadata straight off the `&mut [i32]`
// local (`_len = PtrMetadata(copy _v)`) instead of through a shared reborrow, so this pins
// down that the length `len()` returns still describes the referent the guarded index
// reads.
#[thrust::callable]
fn check(v: &mut [i32], i: usize) {
    if i < v.len() {
        v[i] = 7;
        assert!(v[i] == 7);
    }
}

fn main() {}
