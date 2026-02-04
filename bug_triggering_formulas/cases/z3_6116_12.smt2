(assert (forall ((a Real)) (exists ((b Real)) (forall ((c Real)) (exists ((|| Real)) (forall ((d Real)) (exists ((e Real)) (forall ((h Real)) (exists ((f Real)) (let ((g c)) (let ((i d)(j f)) (let ((k j)(l 0)) (let ((o (<= a l))) (let ((m (or o (<= k i)))(n (<= b g))) (or n m)))))))))))))))
(check-sat)
