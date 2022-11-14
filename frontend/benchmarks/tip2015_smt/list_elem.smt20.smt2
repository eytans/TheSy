(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-const undefined sk)
(declare-fun elem (sk list) Bool)
(declare-fun at (list Int) sk)
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((y Int)) (= (at nil y) undefined)))
(assert
  (forall ((y Int) (z sk) (x2 list))
    (=> (distinct y 0)
      (=> (not (> y 0)) (= (at (cons z x2) y) undefined)))))
(assert
  (forall ((y Int) (z sk) (x2 list))
    (=> (distinct y 0)
      (=> (> y 0) (= (at (cons z x2) y) (at x2 (- y 1)))))))
(assert
  (forall ((y Int) (z sk) (x2 list))
    (=> (= y 0) (= (at (cons z x2) y) z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (exists ((y Int)) (= x (at xs y)))))))
(check-sat)
