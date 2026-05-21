//@check-pass

fn main() {
    let mut call_count = 0;
    let mut s = (
        || {
            call_count = 1;
        },
        0,
    );
    (s.0)();
    assert!(call_count == 1);
}
