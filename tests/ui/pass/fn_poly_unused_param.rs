//@check-pass

fn project_first<T, U, V>(triple: (T, U, V)) -> T {
    triple.0
}

fn chain<A, B, C>(x: A, _phantom_b: B, _phantom_c: C) -> A {
    x
}

fn main() {
    let x = project_first((42, true, 100));
    let y = chain(x, (1, 2), false);
    assert!(y == 42);
}
