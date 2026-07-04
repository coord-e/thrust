//@error-in-other-file: Unsat
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
        let _p = Pair::Two((a, b));
    }
    // wrong: `*a` is 10, not 11
    assert!(*a == 11);
}

fn main() {}
