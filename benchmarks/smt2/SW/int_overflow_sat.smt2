(set-logic QF_BV)
(set-info :status sat)

; Software verification: unsigned integer overflow detection.
; Two 8-bit values x and y, both < 200.
; Assert (x + y) mod 256 < x — this detects unsigned wrap-around.
; SAT: e.g. x = 150, y = 150, sum = 300 mod 256 = 44 < 150.

(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))

; Both values < 200
(assert (bvult x (_ bv200 8)))
(assert (bvult y (_ bv200 8)))

; y must be positive (otherwise no overflow possible)
(assert (not (= y (_ bv0 8))))

; Overflow detection: wrapped sum < x
(assert (bvult (bvadd x y) x))

(check-sat)
(exit)
