//@check-pass
//@compile-flags: -C debug-assertions=off

#[allow(dead_code)]
enum Pair<'a> {
    Two((&'a mut i32, &'a mut i32)),
    None,
}

#[thrust::callable]
fn check(a: &mut i32, b: &mut i32) {
    *a = 10;
    *b = 20;
    {
        // Construct and drop the enum without mutating through the packed references.
        let _p = Pair::Two((a, b));
    }
    // Dropping resolves both prophecies to identity, so the values are unchanged.
    assert!(*a == 10);
    assert!(*b == 20);
}

fn main() {}
