(declare-const __ (_ BitVec 1))
(declare-const x Float64)
(assert (= (fp.to_real x) (fp.to_real (fp (_ bv0 1) (_ bv0 11) ((_ zero_extend 51) __)))))
(check-sat)
