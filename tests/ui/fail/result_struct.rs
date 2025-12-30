//@error-in-other-file: Unsat
//@compile-flags: -C debug-assertions=off

struct Point {
    x: i32,
    y: i32,
}

fn make_point(x: i32, y: i32) -> Result<Point, ()> {
    if x >= 0 && y >= 0 {
        Ok(Point { x, y })
    } else {
        Err(())
    }
}

fn main() {
    let p = make_point(1, 2);
    if let Ok(pt) = p {
        assert!(pt.x > 1);
    }
}
