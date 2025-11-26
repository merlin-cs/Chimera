(declare-fun a (Bool Bool Bool Bool Bool Bool Bool Int Bool Bool Bool Bool Int Bool) Bool)
(assert (forall ((b Bool) (c Bool) (cscf Int) (cscng Bool) (cd Int) (csch Int) (cscni Bool) (cutg Bool) (cuti Bool) (ck Bool) (cm Bool) (ce Bool) (cv Bool) (cn Bool)) (let ((d (distinct c (<= cd 0)))) (let ((e d)(f (= ce (>= cd 0)))) (let ((g (and f ce))) (=> g (a b c b e ck cm cutg cscf cscng cn cv cuti csch cscni)))))))
(check-sat)
