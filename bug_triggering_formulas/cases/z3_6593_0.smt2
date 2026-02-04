(declare-fun c () RoundingMode)
(declare-fun m () Float32)
(assert (and (fp.eq (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp.div c m (fp (_ bv0 1) (_ bv255 8) (_ bv0 23)))) (not (fp.eq (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp.div c m ((_ to_fp 8 24) c (/ (ite (fp.geq (fp (_ bv0 1) (_ bv255 8) (_ bv0 23)) m) 1.0 0.0) 2)))))))
(check-sat)
