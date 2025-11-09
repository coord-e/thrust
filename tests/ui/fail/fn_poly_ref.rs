//@error-in-other-file: Unsat

fn identity_ref<T>(x: &T) -> &T {
    x
}

fn chain_ref<T>(x: &T) -> &T {
    identity_ref(identity_ref(x))
}

fn main() {
    let val = 42;
    let r = chain_ref(&val);
    assert!(*r == 43);
}
