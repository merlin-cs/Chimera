   (declare-sort S 0)

   (declare-sort X 0)

   (declare-sort S 0)

   (declare-sort S 1)

(declare-const x (Option S))
(declare-const y (Option S))
(assert (= x y))
(check-sat)
