(declare-fun a () Real)
(assert (exists ((V Real)) (and (forall ((v Real)) (<= 0 (div (to_int a) (mod 0 (to_int v))))))))
(assert (forall ((v Real)) (distinct true (= 1.0 (sin a)))))
(check-sat)
