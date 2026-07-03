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


(declare-fun p0 (Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p1 (Int A0_Tuple<Array<Int-Int>-Int> Int) Bool)

(declare-fun p2 () Bool)

(declare-fun p3 () Bool)

(declare-fun p4 (Int Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p5 (Int A0_Tuple<Array<Int-Int>-Int> Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p6 (A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) Bool)

(declare-fun p7 (A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>> A0_Tuple<Array<Int-Int>-Int> Int A0_Tuple<Array<Int-Int>-Int> Int) Bool)

(declare-fun p8 (Int Int A0_Tuple<Array<Int-Int>-Int> Int A0_Tuple<Array<Int-Int>-Int> Int) Bool)

(declare-fun p9 (A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p10 (A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p11 (Int A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p12 (Int A0_Tuple<Array<Int-Int>-Int> A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p13 (Int A0_Tuple<Array<Int-Int>-Int> Int Int A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p14 (A0_Tuple<Array<Int-Int>-Int>) Bool)

(declare-fun p15 () Bool)

; c0
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)) (=> (and (= v2 v0) (= v3 v1) (p5 v3 v0 v1 v2) (= v4 v0) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v4) 0) (= v5 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v4) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v4) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v4) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v4) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v4) 0) (= v5 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p7 v5 v0 v1 v2 v3))))

; c1
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v6 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>)) (=> (and (= v2 v0) (= v3 v1) (p5 v3 v0 v1 v2) (= v4 v0) (or (and (> (tuple_proj<Array<Int-Int>-Int>.1 v4) 0) (= v5 (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> (tuple<Int-Tuple<Array<Int-Int>-Int>> (select (tuple_proj<Array<Int-Int>-Int>.0 v4) 0) (tuple<Array<Int-Int>-Int> (lambda ((sub!idx Int)) (ite (and (<= 0 sub!idx) (< sub!idx (- (tuple_proj<Array<Int-Int>-Int>.1 v4) 1))) (select (tuple_proj<Array<Int-Int>-Int>.0 v4) (+ 1 sub!idx)) 0)) (- (tuple_proj<Array<Int-Int>-Int>.1 v4) 1)))))) (and (= (tuple_proj<Array<Int-Int>-Int>.1 v4) 0) (= v5 std.option.Option.None<Tuple<Int-Tuple<Array<Int-Int>-Int>>>)))) (p6 v6))))

; c2
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 Int) (v5 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Int) (v8 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v9 Int) (v10 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v11 Int) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 Int) (v14 Int) (v15 A0_Tuple<Array<Int-Int>-Int>) (v16 Int) (v17 Int)) (=> (and (= v0 0) (= v11 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v10)) (= v13 v9) (p7 v5 v3 v4 v6 v7) (= v6 v3) (= v7 v4) (p5 v7 v3 v4 v6) (= v9 v4) (= v10 v5) (= v12 v6) (= v13 v7) (= v11 0) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v8 v10) (= v1 v12) (= v2 v13) (= v14 v0) (= v15 v1) (= v17 v2) true) (p4 v17 v14 v15))))

; c3
(assert (forall ((v0 Int) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 Int) (v5 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v6 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v7 Int) (v8 Int) (v9 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v10 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v11 A0_Tuple<Array<Int-Int>-Int>) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 Int) (v15 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v16 A0_Tuple<Array<Int-Int>-Int>) (v17 Int) (v18 Int) (v19 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v20 Int) (v21 A0_Tuple<Array<Int-Int>-Int>) (v22 Int) (v23 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v24 Int) (v25 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v26 Int) (v27 A0_Tuple<Array<Int-Int>-Int>) (v28 A0_Tuple<Array<Int-Int>-Int>) (v29 Int) (v30 Int) (v31 A0_Tuple<Array<Int-Int>-Int>) (v32 Int) (v33 Int)) (=> (and (= v4 v1) (= v0 v4) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v5) v25) (= v6 v5) (= v7 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 v6)) (= v8 v7) (= v26 v8) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v9) v25) (= v10 v9) (= v11 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v10)) (= v12 v11) (= v27 v12) (= v29 v24) (= v20 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v19)) (= v22 v18) (p7 v15 v13 v14 v16 v17) (= v16 v13) (= v17 v14) (p5 v17 v13 v14 v16) (= v18 v14) (= v19 v15) (= v21 v16) (= v22 v17) (= v20 1) (= v24 v18) (= v25 v19) (= v28 v21) (= v29 v22) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v23 v25) (= v24 0) (= v1 v26) (= v2 v28) (= v3 v29) (= v30 v0) (= v31 v2) (= v33 v3) true) (p4 v33 v30 v31))))

; c4
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 Int) (v5 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v6 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v7 Int) (v8 Int) (v9 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v10 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v11 A0_Tuple<Array<Int-Int>-Int>) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 Int) (v15 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v16 A0_Tuple<Array<Int-Int>-Int>) (v17 Int) (v18 Int) (v19 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v20 Int) (v21 A0_Tuple<Array<Int-Int>-Int>) (v22 Int) (v23 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v24 Int) (v25 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v26 Int) (v27 A0_Tuple<Array<Int-Int>-Int>) (v28 A0_Tuple<Array<Int-Int>-Int>) (v29 Int) (v30 A0_Tuple<Array<Int-Int>-Int>) (v31 Int) (v32 Int)) (=> (and (= v2 (- v0 1)) (= v4 v0) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v5) v25) (= v6 v5) (= v7 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 v6)) (= v8 v7) (= v26 v8) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v9) v25) (= v10 v9) (= v11 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v10)) (= v12 v11) (= v27 v12) (= v29 v24) (= v20 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v19)) (= v22 v18) (p7 v15 v13 v14 v16 v17) (= v16 v13) (= v17 v14) (p5 v17 v13 v14 v16) (= v18 v14) (= v19 v15) (= v21 v16) (= v22 v17) (= v20 1) (= v24 v18) (= v25 v19) (= v28 v21) (= v29 v22) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v23 v25) (not (= v24 0)) (= v0 v24) (= v1 v27) (= v3 v28) (= v4 v29) (= v30 v1) (= v32 v2) true) (p0 v32 v30))))

; c5
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 Int) (v5 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v6 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v7 Int) (v8 Int) (v9 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v10 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v11 A0_Tuple<Array<Int-Int>-Int>) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 Int) (v15 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v16 A0_Tuple<Array<Int-Int>-Int>) (v17 Int) (v18 Int) (v19 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v20 Int) (v21 A0_Tuple<Array<Int-Int>-Int>) (v22 Int) (v23 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v24 Int) (v25 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v26 Int) (v27 A0_Tuple<Array<Int-Int>-Int>) (v28 A0_Tuple<Array<Int-Int>-Int>) (v29 Int) (v30 A0_Tuple<Array<Int-Int>-Int>) (v31 Int) (v32 Int)) (=> (and (= v2 (- v0 1)) (= v4 v0) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v5) v25) (= v6 v5) (= v7 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 v6)) (= v8 v7) (= v26 v8) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v9) v25) (= v10 v9) (= v11 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v10)) (= v12 v11) (= v27 v12) (= v29 v24) (= v20 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v19)) (= v22 v18) (p7 v15 v13 v14 v16 v17) (= v16 v13) (= v17 v14) (p5 v17 v13 v14 v16) (= v18 v14) (= v19 v15) (= v21 v16) (= v22 v17) (= v20 1) (= v24 v18) (= v25 v19) (= v28 v21) (= v29 v22) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v23 v25) (not (= v24 0)) (= v0 v24) (= v1 v27) (= v3 v28) (= v4 v29) (= v30 v1) (= v31 v2) (p1 v32 v30 v31) true) (p8 v32 v0 v1 v2 v3 v4))))

; c6
(assert (forall ((v0 Int) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Int) (v6 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v7 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v8 Int) (v9 Int) (v10 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v11 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 A0_Tuple<Array<Int-Int>-Int>) (v15 Int) (v16 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v17 A0_Tuple<Array<Int-Int>-Int>) (v18 Int) (v19 Int) (v20 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v21 Int) (v22 A0_Tuple<Array<Int-Int>-Int>) (v23 Int) (v24 A1_Tuple<Int-Tuple<Array<Int-Int>-Int>>) (v25 Int) (v26 A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>) (v27 Int) (v28 A0_Tuple<Array<Int-Int>-Int>) (v29 A0_Tuple<Array<Int-Int>-Int>) (v30 Int) (v31 Int) (v32 A0_Tuple<Array<Int-Int>-Int>) (v33 Int) (v34 Int)) (=> (and (p8 v0 v1 v2 v3 v4 v5) (= v3 (- v1 1)) (= v5 v1) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v6) v26) (= v7 v6) (= v8 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.0 v7)) (= v9 v8) (= v27 v9) (= (std.option.Option.Some<Tuple<Int-Tuple<Array<Int-Int>-Int>>> v10) v26) (= v11 v10) (= v12 (tuple_proj<Int-Tuple<Array<Int-Int>-Int>>.1 v11)) (= v13 v12) (= v28 v13) (= v30 v25) (= v21 (datatype_discr<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v20)) (= v23 v19) (p7 v16 v14 v15 v17 v18) (= v17 v14) (= v18 v15) (p5 v18 v14 v15 v17) (= v19 v15) (= v20 v16) (= v22 v17) (= v23 v18) (= v21 1) (= v25 v19) (= v26 v20) (= v29 v22) (= v30 v23) (matcher_pred<A2_std.option.Option<Tuple<Int-Tuple<Array<Int-Int>-Int>>>> v24 v26) (not (= v25 0)) (= v1 v25) (= v2 v28) (= v4 v29) (= v5 v30) (= v31 v0) (= v32 v4) (= v34 v5) true) (p4 v34 v31 v32))))

; c7
(assert (forall ((v0 Int) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 Int) (v3 Int) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Int)) (=> (and (p4 v2 v0 v1) (= v3 v2) (= v4 v1) (= v5 v0) true) (p1 v5 v4 v3))))

; c8
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 Int)) (=> (and (p0 v2 v0) true) (p5 v2 v0 v2 v0))))

; c9
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Int)) (=> (and (= v1 v0) (p10 v1 v0) (= v2 v0) (= v3 (tuple_proj<Array<Int-Int>-Int>.1 v2))) (p11 v3 v0 v1))))

; c10
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Bool) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v1 (>= v2 2)) (p11 v2 v0 v3) (= v3 v0) (p10 v3 v0) (= v1 false) (= v5 v3) true) (p9 v5))))

; c11
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Bool) (v4 Int) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Int) (v8 Int)) (=> (and (= v1 v0) (= v3 (>= v4 2)) (p11 v4 v2 v5) (= v5 v2) (p10 v5 v2) (not (= v3 false)) (= v0 v2) (= v1 v5) (= v6 v0) (= v8 1) true) (p0 v8 v6))))

; c12
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Bool) (v4 Int) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Int) (v8 Int)) (=> (and (= v1 v0) (= v3 (>= v4 2)) (p11 v4 v2 v5) (= v5 v2) (p10 v5 v2) (not (= v3 false)) (= v0 v2) (= v1 v5) (= v6 v0) (= v7 1) (p1 v8 v6 v7) true) (p12 v8 v0 v1))))

; c13
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Bool) (v6 Int) (v7 A0_Tuple<Array<Int-Int>-Int>) (v8 A0_Tuple<Array<Int-Int>-Int>) (v9 Int) (v10 A0_Tuple<Array<Int-Int>-Int>) (v11 A0_Tuple<Array<Int-Int>-Int>) (v12 Int) (v13 Int)) (=> (and (= v2 1) (= v3 v0) (p12 v9 v8 v10) (= v10 v8) (= v5 (>= v6 2)) (p11 v6 v4 v7) (= v7 v4) (p10 v7 v4) (not (= v5 false)) (= v8 v4) (= v10 v7) (= v0 v8) (= v1 v9) (= v3 v10) (= v11 v0) (= v13 v2) (not (< v13 (tuple_proj<Array<Int-Int>-Int>.1 v11)))) false)))

; c14
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 Int) (v3 A0_Tuple<Array<Int-Int>-Int>) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Bool) (v6 Int) (v7 A0_Tuple<Array<Int-Int>-Int>) (v8 A0_Tuple<Array<Int-Int>-Int>) (v9 Int) (v10 A0_Tuple<Array<Int-Int>-Int>) (v11 A0_Tuple<Array<Int-Int>-Int>) (v12 Int) (v13 Int)) (=> (and (= v2 1) (= v3 v0) (p12 v9 v8 v10) (= v10 v8) (= v5 (>= v6 2)) (p11 v6 v4 v7) (= v7 v4) (p10 v7 v4) (not (= v5 false)) (= v8 v4) (= v10 v7) (= v0 v8) (= v1 v9) (= v3 v10) (= v11 v0) (= v12 v2) (= v13 (select (tuple_proj<Array<Int-Int>-Int>.0 v11) v12))) (p13 v13 v0 v1 v2 v3))))

; c15
(assert (forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 A0_Tuple<Array<Int-Int>-Int>) (v5 Int) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Bool) (v8 Int) (v9 A0_Tuple<Array<Int-Int>-Int>) (v10 A0_Tuple<Array<Int-Int>-Int>) (v11 Int) (v12 A0_Tuple<Array<Int-Int>-Int>) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 Int) (v15 Int) (v16 Int) (v17 A0_Tuple<Array<Int-Int>-Int>) (v18 A0_Tuple<Array<Int-Int>-Int>) (v19 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v0 (= v1 v2)) (= v5 v3) (= v2 v5) (= v15 1) (p13 v16 v13 v14 v15 v17) (= v17 v13) (p12 v11 v10 v12) (= v12 v10) (= v7 (>= v8 2)) (p11 v8 v6 v9) (= v9 v6) (p10 v9 v6) (not (= v7 false)) (= v10 v6) (= v12 v9) (= v13 v10) (= v14 v11) (= v17 v12) (= v1 v14) (= v3 v16) (= v4 v17) (not (= v0 false)) (= v19 v4) true) (p9 v19))))

; c16
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 Int) (v2 A0_Tuple<Array<Int-Int>-Int>) (v3 Bool) (v4 Int) (v5 A0_Tuple<Array<Int-Int>-Int>) (v6 A0_Tuple<Array<Int-Int>-Int>) (v7 Int) (v8 A0_Tuple<Array<Int-Int>-Int>) (v9 A0_Tuple<Array<Int-Int>-Int>) (v10 Int) (v11 Int) (v12 Int) (v13 A0_Tuple<Array<Int-Int>-Int>) (v14 Bool) (v15 Int) (v16 Int) (v17 Int) (v18 A0_Tuple<Array<Int-Int>-Int>)) (=> (and (= v14 (= v15 v16)) (= v1 v17) (= v16 v1) (= v11 1) (p13 v12 v9 v10 v11 v13) (= v13 v9) (p12 v7 v6 v8) (= v8 v6) (= v3 (>= v4 2)) (p11 v4 v2 v5) (= v5 v2) (p10 v5 v2) (not (= v3 false)) (= v6 v2) (= v8 v5) (= v9 v6) (= v10 v7) (= v13 v8) (= v15 v10) (= v17 v12) (= v18 v13) (= v14 false) (= v0 v18) true) false)))

; c17
(assert (forall ((v0 A0_Tuple<Array<Int-Int>-Int>) (v1 A0_Tuple<Array<Int-Int>-Int>)) (=> (and  true) (p10 v1 v1))))

; c18
(assert (=> (and p15 true) p3))

; c19
(assert (=> (and p2 true) p15))

; c20
(assert (=> (and  true) p2))


(check-sat)
