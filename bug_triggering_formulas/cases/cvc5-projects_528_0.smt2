(assert (> real.pi (seq.nth (seq.++ (seq.++ (seq.unit real.pi) (seq.rev (seq.++ (seq.unit real.pi) (seq.unit real.pi)))) (seq.unit real.pi) (seq.unit real.pi)) (seq.len (seq.++ (seq.unit real.pi) (seq.unit real.pi))))))
(check-sat)
