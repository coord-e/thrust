//@error-in-other-file: Unsat
//@rustc-env: THRUST_SOLVER=tests/thrust-pcsat-wrapper COAR_IMAGE=coar:latest

fn update<T>(x: &mut T, new_val: T) {
    *x = new_val;
}

fn chain_update<T>(x: &mut T, temp: T, final_val: T) {
    update(x, temp);
    update(x, final_val);
}

fn main() {
    let mut val = 42;
    chain_update(&mut val, 100, 200);
    assert!(val == 42);
}
