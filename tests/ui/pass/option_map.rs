//@check-pass
//@compile-flags: -C debug-assertions=off
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper

#[thrust::callable]
fn check(opt: Option<i32>) {
    let r = opt.map(|x| x + 1);
    if let Some(i) = opt {
        assert!(r == Some(i + 1));
    }
}

fn main() {}
