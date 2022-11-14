(declare-sort sk 0)
(declare-sort sk2 0)
(declare-fun m (Int) Int)
(assert (forall ((x Int)) (=> (> x 100) (= (m x) (- x 10)))))
(assert
  (forall ((x Int)) (=> (not (> x 100)) (= (m x) (m (m (+ x 11)))))))
