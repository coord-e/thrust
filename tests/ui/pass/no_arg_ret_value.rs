//@check-pass

// A zero-argument function with a non-ZST return: its entry basic block has no
// local-backed parameter, only the synthetic unit parameter that hosts the
// precondition. Exercises the `arg_count == 0` alignment in `drop_bb_zst_params`.
#[thrust_macros::requires(true)]
#[thrust_macros::ensures(result == 5)]
fn five() -> i64 {
    5
}

fn main() {
    assert!(five() == 5);
}
