//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

fn mutate_res(r: &mut Result<i32, i32>) {
    match r {
        Ok(v) => *v += 1,
        Err(e) => *e -= 1,
    }
}

fn main() {
    let mut r = Ok(10);
    mutate_res(&mut r);
    match r {
        Ok(v) => assert!(v == 10),
        Err(_) => unreachable!(),
    }
}
