fn f(x: &mut i64, y: i64) {
    *x = y;
}

fn main() {
    let mut a = 1;
    let b = 2;
    f(&mut a, b);
    assert!(a == b);
}

/*
fn f(_1: &mut i32, _2: i32) -> i32 {
    debug x => _1;
    debug y => _2;
    let mut _0: i32;

    bb0: {
        (*_1) = _2;
        _0 = const 1_i32;
        return;
    }
}

fn main() -> () {
    let mut _0: ();
    let mut _1: i32;
    let _3: i32;
    let mut _4: i32;
    let mut _5: !;
    scope 1 {
        debug a => _1;
        let _2: &mut i32;
        scope 2 {
            debug m => _2;
        }
    }

    bb0: {
        // vars: {}
        // elaborate _1: mut i32 => _1: box i32
        //   template for _1: { <int> | p1 _0 }
        //   rvalue refty: { int | _0 = 1 }
        //   (elaborated) subtype results in c0: p1 _0 <= _0.0 = 1
        // env.bind(_1: { <int> | p1 _0 })
        //   => vars: _1: <_1'>, _1': { int | p1 <_0> }
        _1 = const 1_i32;
        // template for _2: { <int, int> | p2 _0 _1' }
        // rvalue refty: { <int, int> | _0 = <_1', ph0> }
        //   env.mut_borrow(_1)
        //     => vars: _1: <f0>, _1': { int | p1 <_0> }, phs: ph0: int
        // subtype results in c1: p2 _0 _1' <= _0 = <_1', ph0>
        // env.bind(_2: { <int, int> | p2 _0 _1' })
        //   => vars: _1: <f0>, _1': { int | p1 <_0> }, _2: <_2', _2^>, p2 <_2', _2^> _1'
        _2 = &mut _1;
        _3 = f(_2, const 2_i32) -> [return: bb1, unwind continue];
    }

    bb1: {
        _4 = _1;
        switchInt(move _4) -> [2: bb2, otherwise: bb3];
    }

    bb2: {
        return;
    }

    bb3: {
        _5 = core::panicking::panic(const "assertion failed: a == 2") -> unwind continue;
    }
}
*/
