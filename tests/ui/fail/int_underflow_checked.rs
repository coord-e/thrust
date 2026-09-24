//@error-in-other-file: Unsat
//@compile-flags: -C overflow-checks=on

fn pred_above_zero(x: u32) -> u32 {
    if x != 1 {
        x - 1
    } else {
        x
    }
}

fn main() {
    assert!(pred_above_zero(0) == 0);
}
