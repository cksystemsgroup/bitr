(set-logic QF_BV)
(set-info :status unsat)

; Software verification: integer overflow check.
; Two 8-bit unsigned values x and y, both < 100.
; Assert their sum (8-bit, wrapping) > 250.
; Max possible: 99 + 99 = 198 < 250. UNSAT.

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

; Both values are small: x < 100, y < 100
(assert (bvult x (_ bv100 8)))
(assert (bvult y (_ bv100 8)))

; Claim: x + y > 250 (unsigned)
(assert (bvugt (bvadd x y) (_ bv250 8)))

(check-sat)
(exit)
