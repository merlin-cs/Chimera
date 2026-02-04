(declare-const x Real)
(declare-const x4 Real)
(assert (= 0.0 (/ x4 (- real.pi (+ x (* x4 x)) (/ 0 (- x x4))))))
(check-sat)
