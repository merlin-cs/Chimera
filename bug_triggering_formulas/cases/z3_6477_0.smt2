(assert (and false (= (_ bv0 32) (bvor ((_ extract 31 0) ((_ sign_extend 2) ((_ fp.to_sbv 32) RTZ (fp (_ bv0 1) (_ bv2047 11) (_ bv1 52))))) (concat (_ bv0 32))))))
(check-sat)
