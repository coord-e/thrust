(set-logic HORN)

(declare-datatypes ((A0_Mut<Int> 0)) (
  (par () (
    (mut<Int> (mut_current<Int> Int) (mut_final<Int> Int))
  ))
))

(define-fun datatype_discr<A0_Mut<Int>> ((x A0_Mut<Int>)) Int (ite ((_ is mut<Int>) x) 0 (- 1)))
(define-fun matcher_pred<A0_Mut<Int>> ((x0 Int) (x1 Int) (v A0_Mut<Int>)) Bool (or (= v (mut<Int> x0 x1))))

; span=refine_fn_def def_id=take_max local_def_id=DefId(0:3 ~ take_max[e40f]::take_max) krate=take_max 
(declare-fun p0 (A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_fn_def def_id=take_max local_def_id=DefId(0:3 ~ take_max[e40f]::take_max) krate=take_max 
(declare-fun p1 (A0_Mut<Int> A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_fn_def def_id=main local_def_id=DefId(0:5 ~ take_max[e40f]::main) krate=take_max 
(declare-fun p2 () Bool)

; span=refine_fn_def def_id=main local_def_id=DefId(0:5 ~ take_max[e40f]::main) krate=take_max 
(declare-fun p3 () Bool)

; span=refine_basic_block bb=bb3 def=take_max krate=take_max 
(declare-fun p4 (A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb3 def=take_max krate=take_max 
(declare-fun p5 (A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb1 def=take_max krate=take_max 
(declare-fun p6 (A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb1 def=take_max krate=take_max 
(declare-fun p7 (A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb2 def=take_max krate=take_max 
(declare-fun p8 (A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb2 def=take_max krate=take_max 
(declare-fun p9 (A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb0 def=take_max krate=take_max 
(declare-fun p10 (A0_Mut<Int> A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb0 def=take_max krate=take_max 
(declare-fun p11 (A0_Mut<Int> A0_Mut<Int> A0_Mut<Int>) Bool)

; span=ret_template bb=bb0 def=take_max krate=take_max 
(declare-fun p12 (A0_Mut<Int> Bool Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb1 def=take_max krate=take_max 
(declare-fun p13 (A0_Mut<Int> Int Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb2 def=take_max krate=take_max 
(declare-fun p14 (A0_Mut<Int> Int Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb3 def=take_max krate=take_max 
(declare-fun p15 (A0_Mut<Int> Int Int Int Int Int Int Int) Bool)

; span=refine_basic_block bb=bb4 def=main krate=take_max 
(declare-fun p16 () Bool)

; span=refine_basic_block bb=bb4 def=main krate=take_max 
(declare-fun p17 () Bool)

; span=refine_basic_block bb=bb5 def=main krate=take_max 
(declare-fun p18 () Bool)

; span=refine_basic_block bb=bb5 def=main krate=take_max 
(declare-fun p19 () Bool)

; span=refine_basic_block bb=bb3 def=main krate=take_max 
(declare-fun p20 (A0_Mut<Int> Int Int) Bool)

; span=refine_basic_block bb=bb3 def=main krate=take_max 
(declare-fun p21 (Int Int A0_Mut<Int>) Bool)

; span=refine_basic_block bb=bb2 def=main krate=take_max 
(declare-fun p22 (Int Int) Bool)

; span=refine_basic_block bb=bb2 def=main krate=take_max 
(declare-fun p23 (Int Int) Bool)

; span=refine_basic_block bb=bb1 def=main krate=take_max 
(declare-fun p24 (Int) Bool)

; span=refine_basic_block bb=bb1 def=main krate=take_max 
(declare-fun p25 (Int) Bool)

; span=refine_basic_block bb=bb0 def=main krate=take_max 
(declare-fun p26 () Bool)

; span=refine_basic_block bb=bb0 def=main krate=take_max 
(declare-fun p27 () Bool)

; span=analyze_terminator_binds term=_1 = rand() -> [return: bb1, unwind continue] bb=bb0 def=main krate=take_max 
(declare-fun p28 (Int) Bool)

; span=ret_template bb=bb0 def=main krate=take_max 
(declare-fun p29 (Int) Bool)

; span=analyze_terminator_binds term=_2 = rand() -> [return: bb2, unwind continue] bb=bb1 def=main krate=take_max 
(declare-fun p30 (Int Int) Bool)

; span=ret_template bb=bb1 def=main krate=take_max 
(declare-fun p31 (Int Int) Bool)

; span=analyze_terminator_binds term=_3 = take_max(move _10, move _11) -> [return: bb3, unwind continue] bb=bb2 def=main krate=take_max 
(declare-fun p32 (A0_Mut<Int> Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb2 def=main krate=take_max 
(declare-fun p33 (Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb3 def=main krate=take_max 
(declare-fun p34 (Bool Int Int Int Int Int Int Int Int Int) Bool)

; span=ret_template bb=bb4 def=main krate=take_max 
(declare-fun p35 () Bool)

; span=analyze_terminator_binds term=_9 = core::panicking::panic(const "assertion failed: a != b") -> unwind continue bb=bb5 def=main krate=take_max 
(declare-fun p36 () Bool)

; span=ret_template bb=bb5 def=main krate=take_max 
(declare-fun p37 () Bool)

; c0
(assert ; span=analyze_terminator_goto term=switchInt(move _4) -> [0: bb2, otherwise: bb1] bb=bb0 def=take_max krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 A0_Mut<Int>) (v10 A0_Mut<Int>)) (=> (and (= v0 (>= v1 v2)) (= v7 (mut_current<Int> (mut<Int> v4 v3))) (= v1 v7) (= v8 (mut_current<Int> (mut<Int> v6 v5))) (= v2 v8) (p10 (mut<Int> v6 v5) (mut<Int> v4 v3)) (= v0 false) (= (mut_final<Int> (mut<Int> v4 v3)) (mut_current<Int> (mut<Int> v4 v3))) (= v10 (mut<Int> v6 v5)) true) (p8 v10))))

; c1
(assert ; span=analyze_terminator_goto term=switchInt(move _4) -> [0: bb2, otherwise: bb1] bb=bb0 def=take_max krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 A0_Mut<Int>) (v10 A0_Mut<Int>)) (=> (and (= v0 (>= v1 v2)) (= v7 (mut_current<Int> (mut<Int> v4 v3))) (= v1 v7) (= v8 (mut_current<Int> (mut<Int> v6 v5))) (= v2 v8) (p10 (mut<Int> v6 v5) (mut<Int> v4 v3)) (= v0 false) (= (mut_final<Int> (mut<Int> v4 v3)) (mut_current<Int> (mut<Int> v4 v3))) (= v9 (mut<Int> v6 v5)) (p9 v10 v9) true) (p12 v10 v0 v1 v2 v3 v4 v5 v6))))

; c2
(assert ; span=analyze_terminator_goto term=switchInt(move _4) -> [0: bb2, otherwise: bb1] bb=bb0 def=take_max krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 A0_Mut<Int>) (v10 A0_Mut<Int>)) (=> (and (= v0 (>= v1 v2)) (= v7 (mut_current<Int> (mut<Int> v4 v3))) (= v1 v7) (= v8 (mut_current<Int> (mut<Int> v6 v5))) (= v2 v8) (p10 (mut<Int> v6 v5) (mut<Int> v4 v3)) (not (= v0 false)) (= (mut_final<Int> (mut<Int> v6 v5)) (mut_current<Int> (mut<Int> v6 v5))) (= v10 (mut<Int> v4 v3)) true) (p6 v10))))

; c3
(assert ; span=analyze_terminator_goto term=switchInt(move _4) -> [0: bb2, otherwise: bb1] bb=bb0 def=take_max krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 A0_Mut<Int>) (v10 A0_Mut<Int>)) (=> (and (= v0 (>= v1 v2)) (= v7 (mut_current<Int> (mut<Int> v4 v3))) (= v1 v7) (= v8 (mut_current<Int> (mut<Int> v6 v5))) (= v2 v8) (p10 (mut<Int> v6 v5) (mut<Int> v4 v3)) (not (= v0 false)) (= (mut_final<Int> (mut<Int> v6 v5)) (mut_current<Int> (mut<Int> v6 v5))) (= v9 (mut<Int> v4 v3)) (p7 v10 v9) true) (p12 v10 v0 v1 v2 v3 v4 v5 v6))))

; c4
(assert ; span=bb bb=bb0 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 A0_Mut<Int>)) (=> (and (p10 v2 v0) true) (p10 v2 v0))))

; c5
(assert ; span=bb bb=bb0 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 A0_Mut<Int>) (v3 Bool) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int)) (=> (and (p12 v2 v3 v4 v5 v6 v7 v8 v9) (= v0 (mut<Int> v7 v6)) (= v1 (mut<Int> v9 v8)) true) (p11 v2 v0 v1))))

; c6
(assert ; span=analyze_terminator_goto term=goto -> bb3 bb=bb1 def=take_max krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 A0_Mut<Int>) (v8 A0_Mut<Int>)) (=> (and (= (mut<Int> v4 v3) (mut<Int> v1 v2)) (= (mut<Int> v6 v5) (mut<Int> v4 v3)) (p6 (mut<Int> v1 v0)) (= (mut_final<Int> (mut<Int> v2 v0)) (mut_current<Int> (mut<Int> v2 v0))) (= v8 (mut<Int> v6 v5)) true) (p4 v8))))

; c7
(assert ; span=analyze_terminator_goto term=goto -> bb3 bb=bb1 def=take_max krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 A0_Mut<Int>) (v8 A0_Mut<Int>)) (=> (and (= (mut<Int> v4 v3) (mut<Int> v1 v2)) (= (mut<Int> v6 v5) (mut<Int> v4 v3)) (p6 (mut<Int> v1 v0)) (= (mut_final<Int> (mut<Int> v2 v0)) (mut_current<Int> (mut<Int> v2 v0))) (= v7 (mut<Int> v6 v5)) (p5 v8 v7) true) (p13 v8 v0 v1 v2 v3 v4 v5 v6))))

; c8
(assert ; span=bb bb=bb1 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>)) (=> (and (p6 v1) true) (p6 v1))))

; c9
(assert ; span=bb bb=bb1 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int)) (=> (and (p13 v1 v2 v3 v4 v5 v6 v7 v8) (= v0 (mut<Int> v3 v2)) true) (p7 v1 v0))))

; c10
(assert ; span=analyze_terminator_goto term=goto -> bb3 bb=bb2 def=take_max krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 A0_Mut<Int>) (v8 A0_Mut<Int>)) (=> (and (= (mut<Int> v4 v3) (mut<Int> v1 v2)) (= (mut<Int> v6 v5) (mut<Int> v4 v3)) (p8 (mut<Int> v1 v0)) (= (mut_final<Int> (mut<Int> v2 v0)) (mut_current<Int> (mut<Int> v2 v0))) (= v8 (mut<Int> v6 v5)) true) (p4 v8))))

; c11
(assert ; span=analyze_terminator_goto term=goto -> bb3 bb=bb2 def=take_max krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 A0_Mut<Int>) (v8 A0_Mut<Int>)) (=> (and (= (mut<Int> v4 v3) (mut<Int> v1 v2)) (= (mut<Int> v6 v5) (mut<Int> v4 v3)) (p8 (mut<Int> v1 v0)) (= (mut_final<Int> (mut<Int> v2 v0)) (mut_current<Int> (mut<Int> v2 v0))) (= v7 (mut<Int> v6 v5)) (p5 v8 v7) true) (p14 v8 v0 v1 v2 v3 v4 v5 v6))))

; c12
(assert ; span=bb bb=bb2 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>)) (=> (and (p8 v1) true) (p8 v1))))

; c13
(assert ; span=bb bb=bb2 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int)) (=> (and (p14 v1 v2 v3 v4 v5 v6 v7 v8) (= v0 (mut<Int> v3 v2)) true) (p9 v1 v0))))

; c14
(assert ; span=analyze_terminator_goto term=return bb=bb3 def=take_max krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 A0_Mut<Int>)) (=> (and (= (mut<Int> v4 v3) (mut<Int> v1 v2)) (= (mut<Int> v6 v5) (mut<Int> v4 v3)) (p4 (mut<Int> v1 v0)) (= (mut_final<Int> (mut<Int> v2 v0)) (mut_current<Int> (mut<Int> v2 v0))) (= v7 (mut<Int> v6 v5)) true) (p15 v7 v0 v1 v2 v3 v4 v5 v6))))

; c15
(assert ; span=bb bb=bb3 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>)) (=> (and (p4 v1) true) (p4 v1))))

; c16
(assert ; span=bb bb=bb3 def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int)) (=> (and (p15 v1 v2 v3 v4 v5 v6 v7 v8) (= v0 (mut<Int> v3 v2)) true) (p5 v1 v0))))

; c17
(assert ; span=def def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 A0_Mut<Int>)) (=> (and (p0 v2 v0) true) (p10 v2 v0))))

; c18
(assert ; span=def def=take_max krate=take_max 
(forall ((v0 A0_Mut<Int>) (v1 A0_Mut<Int>) (v2 A0_Mut<Int>)) (=> (and (p11 v2 v0 v1) true) (p1 v2 v0 v1))))

; c19
(assert ; span=analyze_terminator_binds term=_1 = rand() -> [return: bb1, unwind continue] bb=bb0 def=main krate=take_max 
(forall ((v0 Int)) (=> (and p26 true) (p28 v0))))

; c20
(assert ; span=analyze_terminator_goto term=_1 = rand() -> [return: bb1, unwind continue] bb=bb0 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int)) (=> (and (p28 v0) p26 (= v2 v0) true) (p24 v2))))

; c21
(assert ; span=analyze_terminator_goto term=_1 = rand() -> [return: bb1, unwind continue] bb=bb0 def=main krate=take_max 
(forall ((v0 Int) (v1 Int)) (=> (and (p28 v0) p26 (= v1 v0) (p25 v1) true) (p29 v0))))

; c22
(assert ; span=bb bb=bb0 def=main krate=take_max 
(=> (and p26 true) p26))

; c23
(assert ; span=bb bb=bb0 def=main krate=take_max 
(forall ((v0 Int)) (=> (and (p29 v0) true) p27)))

; c24
(assert ; span=analyze_terminator_binds term=_2 = rand() -> [return: bb2, unwind continue] bb=bb1 def=main krate=take_max 
(forall ((v0 Int) (v1 Int)) (=> (and (p24 v0) true) (p30 v1 v0))))

; c25
(assert ; span=analyze_terminator_goto term=_2 = rand() -> [return: bb2, unwind continue] bb=bb1 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int)) (=> (and (p30 v1 v0) (p24 v0) (= v2 v0) (= v4 v1) true) (p22 v4 v2))))

; c26
(assert ; span=analyze_terminator_goto term=_2 = rand() -> [return: bb2, unwind continue] bb=bb1 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int)) (=> (and (p30 v1 v0) (p24 v0) (= v2 v0) (= v3 v1) (p23 v2 v3) true) (p31 v0 v1))))

; c27
(assert ; span=bb bb=bb1 def=main krate=take_max 
(forall ((v0 Int) (v1 Int)) (=> (and (p24 v1) true) (p24 v1))))

; c28
(assert ; span=bb bb=bb1 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int)) (=> (and (p31 v1 v2) (= v0 v1) true) (p25 v0))))

; c29
(assert ; span=analyze_terminator_binds term=_3 = take_max(move _10, move _11) -> [return: bb3, unwind continue] bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 Int) (v14 A0_Mut<Int>) (v15 A0_Mut<Int>) (v16 A0_Mut<Int>)) (=> (and (= (mut<Int> v5 v4) (mut<Int> v0 v2)) (= (mut<Int> v7 v6) (mut<Int> v1 v3)) (= (mut<Int> v10 v9) (mut<Int> v5 v8)) (= (mut<Int> v13 v12) (mut<Int> v7 v11)) (p22 v1 v0) (= v14 (mut<Int> v10 v9)) (= v16 (mut<Int> v13 v12)) true) (p0 v16 v14))))

; c30
(assert ; span=analyze_terminator_binds term=_3 = take_max(move _10, move _11) -> [return: bb3, unwind continue] bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 Int) (v14 A0_Mut<Int>) (v15 A0_Mut<Int>) (v16 A0_Mut<Int>)) (=> (and (= (mut<Int> v5 v4) (mut<Int> v0 v2)) (= (mut<Int> v7 v6) (mut<Int> v1 v3)) (= (mut<Int> v10 v9) (mut<Int> v5 v8)) (= (mut<Int> v13 v12) (mut<Int> v7 v11)) (p22 v1 v0) (= v14 (mut<Int> v10 v9)) (= v15 (mut<Int> v13 v12)) (p1 v16 v14 v15) true) (p32 v16 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13))))

; c31
(assert ; span=analyze_terminator_goto term=_3 = take_max(move _10, move _11) -> [return: bb3, unwind continue] bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 Int) (v14 Int) (v15 Int) (v16 Int) (v17 Int) (v18 A0_Mut<Int>) (v19 A0_Mut<Int>)) (=> (and (= (mut<Int> v5 v4) (mut<Int> v0 v2)) (= (mut<Int> v7 v6) (mut<Int> v1 v3)) (= (mut<Int> v10 v9) (mut<Int> v5 v8)) (= (mut<Int> v13 v12) (mut<Int> v7 v11)) (p32 (mut<Int> v15 v14) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13) (p22 v1 v0) (= (mut_final<Int> (mut<Int> v8 v4)) (mut_current<Int> (mut<Int> v8 v4))) (= (mut_final<Int> (mut<Int> v11 v6)) (mut_current<Int> (mut<Int> v11 v6))) (= v16 v2) (= v17 v3) (= v19 (mut<Int> v15 v14)) true) (p20 v19 v16 v17))))

; c32
(assert ; span=analyze_terminator_goto term=_3 = take_max(move _10, move _11) -> [return: bb3, unwind continue] bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 Int) (v14 Int) (v15 Int) (v16 Int) (v17 Int) (v18 A0_Mut<Int>)) (=> (and (= (mut<Int> v5 v4) (mut<Int> v0 v2)) (= (mut<Int> v7 v6) (mut<Int> v1 v3)) (= (mut<Int> v10 v9) (mut<Int> v5 v8)) (= (mut<Int> v13 v12) (mut<Int> v7 v11)) (p32 (mut<Int> v15 v14) v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13) (p22 v1 v0) (= (mut_final<Int> (mut<Int> v8 v4)) (mut_current<Int> (mut<Int> v8 v4))) (= (mut_final<Int> (mut<Int> v11 v6)) (mut_current<Int> (mut<Int> v11 v6))) (= v16 v2) (= v17 v3) (= v18 (mut<Int> v15 v14)) (p21 v16 v17 v18) true) (p33 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))))

; c33
(assert ; span=bb bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int)) (=> (and (p22 v2 v0) true) (p22 v2 v0))))

; c34
(assert ; span=bb bb=bb2 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 Int) (v14 Int) (v15 Int) (v16 Int) (v17 Int)) (=> (and (p33 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17) (= v0 v2) (= v1 v3) true) (p23 v0 v1))))

; c35
(assert ; span=analyze_terminator_goto term=switchInt(move _6) -> [0: bb5, otherwise: bb4] bb=bb3 def=main krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 A0_Mut<Int>)) (=> (and (= v0 (not (= v1 v2))) (= v10 v3) (= v1 v10) (= v11 v4) (= v2 v11) (= (mut<Int> v9 v8) (mut<Int> v6 v7)) (p20 (mut<Int> v6 v5) v3 v4) (= v12 (mut_current<Int> (mut<Int> v9 v8))) (= (mut_final<Int> (mut<Int> v9 v8)) (+ v12 1)) (= v13 (mut<Int> v7 v5)) (= (mut_final<Int> v13) (mut_current<Int> v13)) (= v0 false) true) p18)))

; c36
(assert ; span=analyze_terminator_goto term=switchInt(move _6) -> [0: bb5, otherwise: bb4] bb=bb3 def=main krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 A0_Mut<Int>)) (=> (and (= v0 (not (= v1 v2))) (= v10 v3) (= v1 v10) (= v11 v4) (= v2 v11) (= (mut<Int> v9 v8) (mut<Int> v6 v7)) (p20 (mut<Int> v6 v5) v3 v4) (= v12 (mut_current<Int> (mut<Int> v9 v8))) (= (mut_final<Int> (mut<Int> v9 v8)) (+ v12 1)) (= v13 (mut<Int> v7 v5)) (= (mut_final<Int> v13) (mut_current<Int> v13)) (= v0 false) p19 true) (p34 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9))))

; c37
(assert ; span=analyze_terminator_goto term=switchInt(move _6) -> [0: bb5, otherwise: bb4] bb=bb3 def=main krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 A0_Mut<Int>)) (=> (and (= v0 (not (= v1 v2))) (= v10 v3) (= v1 v10) (= v11 v4) (= v2 v11) (= (mut<Int> v9 v8) (mut<Int> v6 v7)) (p20 (mut<Int> v6 v5) v3 v4) (= v12 (mut_current<Int> (mut<Int> v9 v8))) (= (mut_final<Int> (mut<Int> v9 v8)) (+ v12 1)) (= v13 (mut<Int> v7 v5)) (= (mut_final<Int> v13) (mut_current<Int> v13)) (not (= v0 false)) true) p16)))

; c38
(assert ; span=analyze_terminator_goto term=switchInt(move _6) -> [0: bb5, otherwise: bb4] bb=bb3 def=main krate=take_max 
(forall ((v0 Bool) (v1 Int) (v2 Int) (v3 Int) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int) (v13 A0_Mut<Int>)) (=> (and (= v0 (not (= v1 v2))) (= v10 v3) (= v1 v10) (= v11 v4) (= v2 v11) (= (mut<Int> v9 v8) (mut<Int> v6 v7)) (p20 (mut<Int> v6 v5) v3 v4) (= v12 (mut_current<Int> (mut<Int> v9 v8))) (= (mut_final<Int> (mut<Int> v9 v8)) (+ v12 1)) (= v13 (mut<Int> v7 v5)) (= (mut_final<Int> v13) (mut_current<Int> v13)) (not (= v0 false)) p17 true) (p34 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9))))

; c39
(assert ; span=bb bb=bb3 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 A0_Mut<Int>) (v3 A0_Mut<Int>)) (=> (and (p20 v3 v0 v1) true) (p20 v3 v0 v1))))

; c40
(assert ; span=bb bb=bb3 def=main krate=take_max 
(forall ((v0 Int) (v1 Int) (v2 A0_Mut<Int>) (v3 Bool) (v4 Int) (v5 Int) (v6 Int) (v7 Int) (v8 Int) (v9 Int) (v10 Int) (v11 Int) (v12 Int)) (=> (and (p34 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12) (= v0 v6) (= v1 v7) (= v2 (mut<Int> v9 v8)) true) (p21 v0 v1 v2))))

; c41
(assert ; span=analyze_terminator_goto term=return bb=bb4 def=main krate=take_max 
(=> (and p16 true) p35))

; c42
(assert ; span=bb bb=bb4 def=main krate=take_max 
(=> (and p16 true) p16))

; c43
(assert ; span=bb bb=bb4 def=main krate=take_max 
(=> (and p35 true) p17))

; c44
(assert ; span=analyze_terminator_binds term=_9 = core::panicking::panic(const "assertion failed: a != b") -> unwind continue bb=bb5 def=main krate=take_max 
(=> (and p18 true) false))

; c45
(assert ; span=bb bb=bb5 def=main krate=take_max 
(=> (and p18 true) p18))

; c46
(assert ; span=bb bb=bb5 def=main krate=take_max 
(=> (and p37 true) p19))

; c47
(assert ; span=def def=main krate=take_max 
(=> (and p2 true) p26))

; c48
(assert ; span=def def=main krate=take_max 
(=> (and p27 true) p3))

; c49
(assert ; span=crate krate=take_max 
(=> (and  true) p2))


(check-sat)
