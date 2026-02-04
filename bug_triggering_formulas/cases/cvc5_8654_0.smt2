(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (forall ((c Bool) (d Bool)) (or (and a d) (and b d) (and c d))))
(check-sat)
