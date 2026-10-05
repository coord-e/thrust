//@check-pass
//@compile-flags: -C debug-assertions=off

struct Cache {
    page: Box<i64>,
}

impl thrust_models::Model for Cache {
    type Ty = Self;
}

fn main() {
    let mut c = Cache { page: Box::new(1) };
    c.page = Box::new(5);
    assert!(*c.page == 5);
}
