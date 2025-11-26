(declare-const x Real)
(assert (forall ((a Real) (v Real) (r Real)) (< (* x (+ v (* x r))) (* (- 1.0 a) (- 1.0 (* v v v))))))
(check-sat)
