(set-logic QF_ABV)
(set-info :status unsat)

; Software verification: buffer overflow check.
; Array buf[256] of bytes indexed by 8-bit address.
; Write value 0x42 at index i where i < 10 (unsigned).
; Original buf has 0x00 at index 10.
; Assert that reading index 10 from modified array yields 0x42.
; Since i in {0..9}, index 10 is untouched, still 0x00. UNSAT.

(declare-fun buf () (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const i (_ BitVec 8))

; Bound: i < 10
(assert (bvult i (_ bv10 8)))

; Original buffer has 0x00 at index 10
(assert (= (select buf (_ bv10 8)) (_ bv0 8)))

; Write 0x42 at index i
(define-fun buf1 () (Array (_ BitVec 8) (_ BitVec 8))
  (store buf i (_ bv66 8)))

; Claim: reading index 10 from buf1 yields 0x42 (66 decimal)
(assert (= (select buf1 (_ bv10 8)) (_ bv66 8)))

(check-sat)
(exit)
