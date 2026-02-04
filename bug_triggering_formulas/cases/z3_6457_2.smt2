(declare-const a (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const b (Array (_ BitVec 32) (_ BitVec 32)))
(assert (let ((c ((_ zero_extend 16) ((_ zero_extend 1) ((_ zero_extend 13) (_ bv0 2)))))) (distinct (_ bv0 32) (ite (bvult (_ bv0 32) ((_ fp.to_ubv 32) roundTowardZero (fp.mul roundTowardPositive (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) ((_ to_fp 8 24) (select (store (store b (_ bv0 32) (select a (_ bv0 32))) (select a (_ bv0 32)) (_ bv0 32)) (_ bv0 32)))))) (_ bv1 32) (_ bv0 32)))))
(check-sat)
