(set-logic QF_BV)
(set-info :status sat)

; Software verification: loop unrolling / bounded model checking.
; Model a loop: i starts at 0, increments by 3 each iteration.
;   for (uint8_t i = 0, step = 0; step < 5; step++) i += 3;
; After 5 iterations: i = 0+3+3+3+3+3 = 15.
; Assert i == 15 after 5 steps. SAT.

(declare-const i0 (_ BitVec 8))

; Initial value
(assert (= i0 (_ bv0 8)))

; Unroll 5 loop iterations using let bindings
(assert
  (let ((i1 (bvadd i0 (_ bv3 8))))
    (let ((i2 (bvadd i1 (_ bv3 8))))
      (let ((i3 (bvadd i2 (_ bv3 8))))
        (let ((i4 (bvadd i3 (_ bv3 8))))
          (let ((i5 (bvadd i4 (_ bv3 8))))
            (= i5 (_ bv15 8))))))))

(check-sat)
(exit)
