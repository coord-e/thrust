//@check-pass
//@compile-flags: -C overflow-checks=on

fn succ_below_max(x: i64) -> i64 {
    if x != 9223372036854775807 {
        x + 1
    } else {
        x
    }
}

fn main() {
    assert!(succ_below_max(9223372036854775807) == 9223372036854775807);
}
