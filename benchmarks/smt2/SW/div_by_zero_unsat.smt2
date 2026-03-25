(set-logic QF_BV)
(set-info :status unsat)

; Software verification: division-by-zero guard.
; A defensive check asserts both that x == 0 and x != 0.
; Models a contradictory path condition from symbolic execution
; where a division guard (x != 0) conflicts with an error path (x == 0).
; UNSAT: no value of x satisfies both constraints simultaneously.

(declare-const x (_ BitVec 8))

; Error path requires x == 0 (division by zero)
(assert (= x (_ bv0 8)))

; But guard requires x != 0
(assert (not (= x (_ bv0 8))))

(check-sat)
(exit)
