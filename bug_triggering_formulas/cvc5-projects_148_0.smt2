(declare-const arr1 (Array Int Bool))
(assert (select arr1 33))
(check-sat)
