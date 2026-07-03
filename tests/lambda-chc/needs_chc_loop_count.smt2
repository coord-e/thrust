(set-logic HORN)

(declare-datatypes ((A0_Mut<Int> 0) (A2_Tuple<Int-Tuple<Array<Int-Int>-Int>> 0) (A1_Tuple<Array<Int-Int>-Int> 0) (A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> 0)) (
  (par () (
    (mut<Int> (mut_current<Int> Int) (mut_final<Int> Int))
  ))
  (par () (
    (tuple<Int-Tuple<Array<Int-Int>-Int>> (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 Int) (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 A1_Tuple<Array<Int-Int>-Int>))
  ))
  (par () (
    (tuple<Array<Int-Int>-Int> (tuple_proj<Array<Int-Int>-Int>.0 (Array Int Int)) (tuple_proj<Array<Int-Int>-Int>.1 Int))
  ))
  (par () (
    (std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>> )
    (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (_getstd.option.Option.Some.0<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>))
  ))
))

(define-fun datatype_discr<A0_Mut<Int>> ((x A0_Mut<Int>)) Int (ite ((_ is mut<Int>) x) 0 (- 1)))
(define-fun matcher_pred<A0_Mut<Int>> ((x0 Int) (x1 Int) (v A0_Mut<Int>)) Bool (or (= v (mut<Int> x0 x1))))
(define-fun datatype_discr<A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>> ((x A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) Int (ite ((_ is tuple<Int-Tuple<Array<Int-Int>-Int>>) x) 0 (- 1)))
(define-fun matcher_pred<A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>> ((x0 Int) (x1 A1_Tuple<Array<Int-Int>-Int>) (v A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) Bool (or (= v (tuple<Int-Tuple<Array<Int-Int>-Int>> x0 x1))))
(define-fun datatype_discr<A1_Tuple<Array<Int-Int>-Int>> ((x A1_Tuple<Array<Int-Int>-Int>)) Int (ite ((_ is tuple<Array<Int-Int>-Int>) x) 0 (- 1)))
(define-fun matcher_pred<A1_Tuple<Array<Int-Int>-Int>> ((x0 (Array Int Int)) (x1 Int) (v A1_Tuple<Array<Int-Int>-Int>)) Bool (or (= v (tuple<Array<Int-Int>-Int> x0 x1))))
(define-fun datatype_discr<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> ((x A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) Int (ite ((_ is std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) x) 0 (ite ((_ is std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) x) 1 (- 1))))
(define-fun matcher_pred<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> ((x0 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) Bool (or (= v std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (= v (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> x0))))
(define-fun-rec seq_concat<Int> ((s A1_Tuple<Array<Int-Int>-Int>) (t A1_Tuple<Array<Int-Int>-Int>)) (Array Int Int) (ite (<= (tuple_proj<Array<Int-Int>-Int>.1 t) 0) (tuple_proj<Array<Int-Int>-Int>.0 s) (store (seq_concat<Int> s (tuple<Array<Int-Int>-Int> (tuple_proj<Array<Int-Int>-Int>.0 t) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1))) (+ (tuple_proj<Array<Int-Int>-Int>.1 s) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1)) (select (tuple_proj<Array<Int-Int>-Int>.0 t) (- (tuple_proj<Array<Int-Int>-Int>.1 t) 1)))))


(declare-fun p0 () Bool)

(declare-fun p1 () Bool)

(declare-fun p2 (A1_Tuple<Array<Int-Int>-Int> A1_Tuple<Array<Int-Int>-Int> A1_Tuple<Array<Int-Int>-Int> Int) Bool)

(declare-fun p3 (A1_Tuple<Array<Int-Int>-Int> A1_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p4 (A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) Bool)

(declare-fun p5 (A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A1_Tuple<Array<Int-Int>-Int> A1_Tuple<Array<Int-Int>-Int> A1_Tuple<Array<Int-Int>-Int> Int A1_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p6 (Int A1_Tuple<Array<Int-Int>-Int> Int Int A1_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p7 (A1_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p8 () Bool)

; c0
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 A1_Tuple<Array<Int-Int>-Int>) (v2 A1_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A1_Tuple<Array<Int-Int>-Int>) (v5 A1_Tuple<Array<Int-Int>-Int>) (v6 Int) (v7 A1_Tuple<Array<Int-Int>-Int>) (v8 A1_Tuple<Array<Int-Int>-Int>)) (=> (and (= v2 v0) (= v3 0) (= v1 v0) (p3 v1 v0) (= v4 v0) (= v5 v2) (= v6 v3) (= v8 v1) true) (p2 v8 v4 v5 v6))))

; c1
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 A1_Tuple<Array<Int-Int>-Int>) (v2 A1_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A1_Tuple<Array<Int-Int>-Int>) (v5 A1_Tuple<Array<Int-Int>-Int>) (v6 A1_Tuple<Array<Int-Int>-Int>) (v7 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) (=> (and (= v5 v2) (= v1 v5) (= v4 v0) (p2 v4 v0 v2 v3) (= v6 v1) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v6) 0) (= v7 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v6) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v6) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v6) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v6) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v6) 0) (= v7 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p5 v7 v0 v1 v2 v3 v4))))

; c2
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 A1_Tuple<Array<Int-Int>-Int>) (v2 A1_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A1_Tuple<Array<Int-Int>-Int>) (v5 A1_Tuple<Array<Int-Int>-Int>) (v6 A1_Tuple<Array<Int-Int>-Int>) (v7 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v8 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) (=> (and (= v5 v2) (= v1 v5) (= v4 v0) (p2 v4 v0 v2 v3) (= v6 v1) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v6) 0) (= v7 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v6) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v6) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v6) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v6) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v6) 0) (= v7 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p4 v8))))

; c3
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 Int) (v3 A1_Tuple<Array<Int-Int>-Int>) (v4 Int) (v5 A1_Tuple<Array<Int-Int>-Int>) (v6 A1_Tuple<Array<Int-Int>-Int>) (v7 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v8 A1_Tuple<Array<Int-Int>-Int>) (v9 A1_Tuple<Array<Int-Int>-Int>) (v10 Int) (v11 A1_Tuple<Array<Int-Int>-Int>) (v12 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v13 A1_Tuple<Array<Int-Int>-Int>) (v14 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v15 Int) (v16 Int) (v17 A1_Tuple<Array<Int-Int>-Int>) (v18 A1_Tuple<Array<Int-Int>-Int>) (v19 Int)) (=> (and (= v4 v2) (= v1 v4) (= v3 v0) (= v15 (datatype_discr<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v14)) (= v17 v13) (p5 v7 v6 v8 v9 v10 v11) (= v5 v9) (= v8 v5) (= v11 v6) (p2 v11 v6 v9 v10) (= v13 v6) (= v16 v10) (= v14 v7) (= v17 v11) (= v15 0) (matcher_pred<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v12 v14) (= v0 v13) (= v2 v16) (= v3 v17) (= v18 v0) (= v19 (tuple_proj<Array<Int-Int>-Int>.1 v18))) (p6 v19 v0 v1 v2 v3))))

; c4
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 A1_Tuple<Array<Int-Int>-Int>) (v3 A1_Tuple<Array<Int-Int>-Int>) (v4 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v5 A1_Tuple<Array<Int-Int>-Int>) (v6 A1_Tuple<Array<Int-Int>-Int>) (v7 Int) (v8 A1_Tuple<Array<Int-Int>-Int>) (v9 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v10 A1_Tuple<Array<Int-Int>-Int>) (v11 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v12 Int) (v13 Int) (v14 A1_Tuple<Array<Int-Int>-Int>) (v15 A1_Tuple<Array<Int-Int>-Int>) (v16 Bool) (v17 Int) (v18 Int) (v19 Int) (v20 A1_Tuple<Array<Int-Int>-Int>)) (=> (and (= v16 (= v17 v18)) (= v1 v19) (= v17 v1) (p6 v18 v15 v17 v19 v20) (= v20 v15) (= v12 (datatype_discr<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v11)) (= v14 v10) (p5 v4 v3 v5 v6 v7 v8) (= v2 v6) (= v5 v2) (= v8 v3) (p2 v8 v3 v6 v7) (= v10 v3) (= v13 v7) (= v11 v4) (= v14 v8) (= v12 0) (matcher_pred<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v9 v11) (= v15 v10) (= v19 v13) (= v20 v14) (= v16 false) (= v0 v20) true) false)))

; c5
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v2 Int) (v3 A1_Tuple<Array<Int-Int>-Int>) (v4 A1_Tuple<Array<Int-Int>-Int>) (v5 Int) (v6 Int) (v7 Int) (v8 A1_Tuple<Array<Int-Int>-Int>) (v9 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v10 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v11 A1_Tuple<Array<Int-Int>-Int>) (v12 A1_Tuple<Array<Int-Int>-Int>) (v13 A1_Tuple<Array<Int-Int>-Int>) (v14 A1_Tuple<Array<Int-Int>-Int>) (v15 A1_Tuple<Array<Int-Int>-Int>) (v16 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v17 A1_Tuple<Array<Int-Int>-Int>) (v18 A1_Tuple<Array<Int-Int>-Int>) (v19 Int) (v20 A1_Tuple<Array<Int-Int>-Int>) (v21 A1_Tuple<Array<Int-Int>-Int>) (v22 A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v23 Int) (v24 Int) (v25 A1_Tuple<Array<Int-Int>-Int>) (v26 A2_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v27 Int) (v28 A1_Tuple<Array<Int-Int>-Int>) (v29 A1_Tuple<Array<Int-Int>-Int>) (v30 Int) (v31 A1_Tuple<Array<Int-Int>-Int>) (v32 A1_Tuple<Array<Int-Int>-Int>)) (=> (and (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v9) v1) (= v10 v9) (= v11 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v10)) (= v12 v11) (= v4 v12) (= (mut<Int> v7 v6) (mut<Int> v2 v5)) (= v13 v4) (= v8 v13) (= v3 v0) (= v23 (datatype_discr<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v22)) (= v25 v21) (p5 v16 v15 v17 v18 v19 v20) (= v14 v18) (= v17 v14) (= v20 v15) (p2 v20 v15 v18 v19) (= v21 v15) (= v24 v19) (= v22 v16) (= v25 v20) (= v23 1) (= v0 v21) (= v2 v24) (= v1 v22) (= v3 v25) (matcher_pred<A3_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v26 v1) (= v27 (mut_current<Int> (mut<Int> v7 v6))) (= (mut_final<Int> (mut<Int> v7 v6)) (+ v27 1)) (= v28 v0) (= v29 v8) (= v30 v5) (= v32 v3) true) (p2 v32 v28 v29 v30))))

; c6
(assert (forall ((v0 A1_Tuple<Array<Int-Int>-Int>) (v1 A1_Tuple<Array<Int-Int>-Int>)) (=> (and  true) (p3 v1 v1))))

; c7
(assert (=> (and p8 true) p1))

; c8
(assert (=> (and p0 true) p8))

; c9
(assert (=> (and  true) p0))


(check-sat)
