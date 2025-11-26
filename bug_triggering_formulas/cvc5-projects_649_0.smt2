(assert (fp.leq (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp.max (fp.max (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv1 1) (_ bv0 8) (_ bv0 23))) (fp.abs (fp.max (fp (_ bv0 1) (_ bv0 8) (_ bv0 23)) (fp (_ bv1 1) (_ bv0 8) (_ bv0 23)))))))
(check-sat)
