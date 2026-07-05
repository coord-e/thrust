//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result.length == v.length + 2)]
#[thrust_macros::invariant_context]
fn push_two(v: Vec<i64>) -> Vec<i64> {
    let mut w = v;
    let mut i = 0_i64;
    while i < 2 {
        thrust_macros::invariant!(
            |i: i64, w: Vec<i64>, v: thrust_models::FnParam<Vec<i64>>|
                w.length == v.at_entry().length + i && i <= 2
        );
        w.push(i);
        w.push(i);
        i += 1;
    }
    w
}

fn main() {
    let v = push_two(Vec::new());
    assert!(v.len() == 2);
}
