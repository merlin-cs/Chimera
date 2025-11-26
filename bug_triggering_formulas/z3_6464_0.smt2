(assert (not (distinct (_ bv0 1) (ite (fp.lt (_ +zero 2 6) (fp (_ bv0 1) (_ bv0 2) (_ bv0 5))) (_ bv1 1) (_ bv0 1)))))
(check-sat)
