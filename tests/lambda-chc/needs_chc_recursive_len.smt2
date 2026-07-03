(set-logic HORN)

(declare-datatypes ((A1_Tuple<Int-Tuple<Array<Int-Int>-Int>> 0) (A0_Tuple<Array<Int-Int>-Int> 0) (A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> 0)) (
  (par () (
    (tuple<Int-Tuple<Array<Int-Int>-Int>> (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 Int) (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 A0_Tuple<Array<Int-Int>-Int>))
  ))
  (par () (
    (tuple<Array<Int-Int>-Int> (tuple_proj<Array<Int-Int>-Int>.0 (Array Int Int)) (tuple_proj<Array<Int-Int>-Int>.1 Int))
  ))
  (par () (
    (std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>> )
    (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (_getstd.option.Option.Some.0<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>))
  ))
))

(define-fun datatype_discr<A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>> ((x A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) Int (ite ((_ is tuple<Int-Tuple<Array<Int-Int>-Int>>) x) 0 (- 1)))
(define-fun matcher_pred<A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>> ((x0 Int) (x1 A0_Tuple<Array<Int-Int>-Int>) (v A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) Bool (or (= v (tuple<Int-Tuple<Array<Int-Int>-Int>> x0 x1))))
(define-fun datatype_discr<A0_Tuple<Array<Int-Int>-Int>> ((x A0_Tuple<Array<Int-Int>-Int>)) Int (ite ((_ is tuple<Array<Int-Int>-Int>) x) 0 (- 1)))
(define-fun matcher_pred<A0_Tuple<Array<Int-Int>-Int>> ((x0 (Array Int Int)) (x1 Int) (v A0_Tuple<Array<Int-Int>-Int>)) Bool (or (= v (tuple<Array<Int-Int>-Int> x0 x1))))
(define-fun datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> ((x A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) Int (ite ((_ is std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) x) 0 (ite ((_ is std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) x) 1 (- 1))))
(define-fun matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> ((x0 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) Bool (or (= v std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (= v (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> x0))))
(define-fun-rec seq_concat<Int> ((s A0_Tuple<Array<Int-Int>-Int>) (t A0_Tuple<Array<Int-Int>-Int>)) (Array Int Int) (ite (<= (tuple_proj<Array<Int-Int>-Int>.1 t) 0) (tuple_proj<Array<Int-Int>-Int>.0 s) (store (seq_concat<Int> s (tuple<Array<Int-Int>-Int> (tuple_proj<Array<Int-Int>-Int>.0 t) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1))) (+ (tuple_proj<Array<Int-Int>-Int>.1 s) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1)) (select (tuple_proj<Array<Int-Int>-Int>.0 t) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1)))))


(declare-fun p0 (A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p1 (Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p2 () Bool)

(declare-fun p3 () Bool)

(declare-fun p4 (A0_Tuple<Array<Int-Int>-Int> Int) Bool)

(declare-fun p5 (A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p6 (A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) Bool)

(declare-fun p7 (A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p8 (Int A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p9 (A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p10 (Int A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p11 (Int A0_Tuple<Array<Int-Int>-Int> Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p12 (A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p13 () Bool)

; c0
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) (=> (and (= v1 v0) (p5 v1 v0) (= v2 v0) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v2) 0) (= v3 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v2) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v2) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v2) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v2) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v2) 0) (= v3 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p7 v3 v0 v1))))

; c1
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v4 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) (=> (and (= v1 v0) (p5 v1 v0) (= v2 v0) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v2) 0) (= v3 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v2) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v2) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v2) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v2) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v2) 0) (= v3 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p6 v4))))

; c2
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v6 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v7 Int) (v8 A0_Tuple<Array<Int-Int>-Int>) (v9 Int) (v10 A0_Tuple<Array<Int-Int>-Int>) (v11 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v0 0) (= v7 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v6)) (p7 v3 v2 v4) (= v4 v2) (p5 v4 v2) (= v6 v3) (= v8 v4) (= v7 0) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v5 v6) (= v1 v8) (= v9 v0) (= v11 v1) true) (p4 v11 v9))))

; c3
(assert (forall ((v0 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v4 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 A0_Tuple<Array<Int-Int>-Int>) (v8 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v9 A0_Tuple<Array<Int-Int>-Int>) (v10 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v11 Int) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v14 A0_Tuple<Array<Int-Int>-Int>) (v15 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v3) v0) (= v4 v3) (= v5 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v4)) (= v6 v5) (= v1 v6) (= v11 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v10)) (p7 v8 v7 v9) (= v9 v7) (p5 v9 v7) (= v10 v8) (= v12 v9) (= v11 1) (= v0 v10) (= v2 v12) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v13 v0) (= v15 v1) true) (p0 v15))))

; c4
(assert (forall ((v0 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v4 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 A0_Tuple<Array<Int-Int>-Int>) (v8 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v9 A0_Tuple<Array<Int-Int>-Int>) (v10 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v11 Int) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v14 A0_Tuple<Array<Int-Int>-Int>) (v15 Int)) (=> (and (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v3) v0) (= v4 v3) (= v5 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v4)) (= v6 v5) (= v1 v6) (= v11 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v10)) (p7 v8 v7 v9) (= v9 v7) (p5 v9 v7) (= v10 v8) (= v12 v9) (= v11 1) (= v0 v10) (= v2 v12) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v13 v0) (= v14 v1) (p1 v15 v14) true) (p8 v15 v0 v1 v2))))

; c5
(assert (forall ((v0 Int) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v4 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 A0_Tuple<Array<Int-Int>-Int>) (v8 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v9 A0_Tuple<Array<Int-Int>-Int>) (v10 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v11 Int) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v14 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v15 A0_Tuple<Array<Int-Int>-Int>) (v16 Int) (v17 A0_Tuple<Array<Int-Int>-Int>) (v18 Int) (v19 A0_Tuple<Array<Int-Int>-Int>) (v20 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v0 (+ 1 v1)) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v3) v14) (= v4 v3) (= v5 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v4)) (= v6 v5) (= v15 v6) (p8 v16 v14 v15 v17) (= v11 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v10)) (p7 v8 v7 v9) (= v9 v7) (p5 v9 v7) (= v10 v8) (= v12 v9) (= v11 1) (= v14 v10) (= v17 v12) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v13 v14) (= v1 v16) (= v2 v17) (= v18 v0) (= v20 v2) true) (p4 v20 v18))))

; c6
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int)) (=> (and (p4 v1 v0) (= v2 v1) (= v3 v0) true) (p1 v3 v2))))

; c7
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (p0 v1) true) (p5 v1 v1))))

; c8
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v1 v0) (p9 v1 v0) (= v3 v0) true) (p0 v3))))

; c9
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int)) (=> (and (= v1 v0) (p9 v1 v0) (= v2 v0) (p1 v3 v2) true) (p10 v3 v0 v1))))

; c10
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 Int) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Int)) (=> (and (= v2 v0) (p10 v4 v3 v5) (= v5 v3) (p9 v5 v3) (= v0 v3) (= v1 v4) (= v2 v5) (= v6 v0) (= v7 (tuple_proj<Array<Int-Int>-Int>.1 v6))) (p11 v7 v0 v1 v2))))

; c11
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Bool) (v6 Int) (v7 Int) (v8 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v5 (= v6 v7)) (p11 v7 v4 v6 v8) (= v8 v4) (p10 v2 v1 v3) (= v3 v1) (p9 v3 v1) (= v4 v1) (= v6 v2) (= v8 v3) (= v5 false) (= v0 v8) true) false)))

; c12
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>)) (=> (and  true) (p9 v1 v1))))

; c13
(assert (=> (and p13 true) p3))

; c14
(assert (=> (and p2 true) p13))

; c15
(assert (=> (and  true) p2))


(check-sat)
