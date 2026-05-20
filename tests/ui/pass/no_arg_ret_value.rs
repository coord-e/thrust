//@check-pass

// A zero-argument function with a non-ZST return value. Its `RETURN_PLACE` is
// not live at entry and there is no live ZST local, so the entry basic block
// exposes no local-backed parameter: its function type carries only the
// synthetic unit parameter (with no backing local) that hosts the precondition.
// This exercises the `arg_count == 0` alignment in `drop_bb_zst_params`, which
// must keep exactly one parameter so the entry type matches the expected type.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn five() -> i64 {
    5
}

fn main() {
    assert!(five() == 5);
}
