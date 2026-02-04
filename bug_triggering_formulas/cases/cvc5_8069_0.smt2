(assert (fp.geq (fp (_ bv0 1) (_ bv0 15) (_ bv0 63)) ((_ to_fp 15 64) ((_ zero_extend 16) ((_ extract 62 0) (concat (_ bv0 32) (_ bv0 31)))))))
(check-sat)
