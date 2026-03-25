(set-logic QF_BV)
(set-info :status unsat)

; Software verification: bitfield packing constraint.
; A 16-bit register with specific field assignments:
;   bits [3:0]  = 0xA  (field A)
;   bits [7:4]  = 0x5  (field B)
;   bits [15:8] = 0x00 (reserved, must be zero)
; The only value satisfying all three is 0x005A.
; Assert the full value != 0x005A. UNSAT.

(declare-const reg (_ BitVec 16))

; Field A: bits [3:0] == 0xA
(assert (= ((_ extract 3 0) reg) #xA))

; Field B: bits [7:4] == 0x5
(assert (= ((_ extract 7 4) reg) #x5))

; Reserved: bits [15:8] == 0x00
(assert (= ((_ extract 15 8) reg) #x00))

; Claim: the register is NOT 0x005A
(assert (not (= reg #x005A)))

(check-sat)
(exit)
