//@check-pass

struct Align {
    pow2: u8,
}

impl Align {
    const EIGHT: Align = Align { pow2: 3 };
}

fn main() {
    let a = Align::EIGHT;
    assert!(a.pow2 == 3);
}
