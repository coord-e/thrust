//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(true)]
#[thrust::trusted]
fn rand() -> i64 { unimplemented!() }

#[thrust_macros::context]
trait Foo {
    #[thrust_macros::invariant_context]
    fn run(&mut self) {
        let mut x: i64 = 0;
        while rand() == 0 {
            thrust_macros::invariant!(|x: i64| x >= 1);
            x += 1;
        }
        assert!(x >= 0);
    }
}

struct Bar;
impl thrust_models::Model for Bar {
    type Ty = ();
}
impl Foo for Bar {}

fn main() {
    Bar.run();
}
