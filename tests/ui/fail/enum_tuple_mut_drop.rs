//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

// Companion to `pass/enum_tuple_mut_drop.rs`: the enum-drop path must not lose a
// packed prophecy. Dropping resolves both references to identity, so `*a` is 10,
// not 11, and this assertion must be rejected.
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
        let _p = Pair::Two((a, b));
    }
    // wrong: `*a` is 10, not 11
    assert!(*a == 11);
}

fn main() {}
