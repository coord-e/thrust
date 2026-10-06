//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

fn diagonal(grid: &[&[i64]], i: usize) -> i64 {
    grid[i][i]
}

fn main() {
    let row0 = [1, 2];
    let row1 = [3, 4];
    let rows: [&[i64]; 2] = [&row0, &row1];
    assert!(diagonal(&rows, 1) == 4);
}
