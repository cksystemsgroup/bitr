(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvand x (bvnot x)) (_ bv1 8)))
(check-sat)
