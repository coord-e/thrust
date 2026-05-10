//@check-pass

struct S(i32);

fn main() {
    let x = &S(42);
    assert!(x.0 == 42);
}
