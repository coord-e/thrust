//@check-pass
//@compile-flags: -C debug-assertions=off

// Regression test: dropping an enum whose variant field is a *tuple of mutable
// references* used to panic in `refine/env.rs` (`assert!(assumption_existentials
// .is_empty())`) because the drop assumption for the aggregate field introduced
// existentials the enum-drop path did not expect. Dropping such a value must
// resolve every packed prophecy to identity.
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
