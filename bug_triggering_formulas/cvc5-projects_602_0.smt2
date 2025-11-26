(assert (forall ((x RoundingMode)) (distinct (= RTZ x) (distinct x roundNearestTiesToEven))))
(check-sat)
