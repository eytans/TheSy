(declare-fun sum (Int) Int)
(declare-fun cubes (Int) Int)
(assert (forall ((x Int)) (=> (= x 0) (= (sum x) 0))))
(assert
  (forall ((x Int))
    (=> (distinct x 0) (= (sum x) (+ (sum (- x 1)) x)))))
(assert (forall ((x Int)) (=> (= x 0) (= (cubes x) 0))))
(assert
  (forall ((x Int))
    (=> (distinct x 0)
      (= (cubes x) (+ (cubes (- x 1)) (* (* x x) x))))))
(assert (not (forall ((n Int)) (= (cubes n) (* (sum n) (sum n))))))
(check-sat)
