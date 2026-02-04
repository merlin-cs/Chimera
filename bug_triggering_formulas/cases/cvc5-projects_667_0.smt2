(assert (>= real.pi (/ real.pi (cot (- (arccos (sin real.pi)))))))
(check-sat)
