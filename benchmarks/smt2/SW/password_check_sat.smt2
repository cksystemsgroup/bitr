(set-logic QF_BV)
(set-info :status sat)

; Software verification: password / license key check.
; A 4-byte password is XOR'd with a known key, and the result
; must match an expected ciphertext. Find the password.
;
; key  = [0xAA, 0xBB, 0xCC, 0xDD]
; want = [0xDE, 0xAD, 0xBE, 0xEF]
; password[i] = key[i] XOR want[i]
;            = [0x74, 0x16, 0x72, 0x32]
; SAT: the solver finds the unique password.

(declare-const p0 (_ BitVec 8))
(declare-const p1 (_ BitVec 8))
(declare-const p2 (_ BitVec 8))
(declare-const p3 (_ BitVec 8))

; XOR with key must produce expected hash
(assert (= (bvxor p0 #xAA) #xDE))
(assert (= (bvxor p1 #xBB) #xAD))
(assert (= (bvxor p2 #xCC) #xBE))
(assert (= (bvxor p3 #xDD) #xEF))

(check-sat)
(exit)
