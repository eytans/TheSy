(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun takeWhile (fun12 list) list)
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(assert (forall ((x fun12)) (= (takeWhile x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (apply12 x z)
      (= (takeWhile x (cons z xs)) (cons z (takeWhile x xs))))))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (not (apply12 x z)) (= (takeWhile x (cons z xs)) nil))))
(assert (forall ((x sk)) (apply12 lam x)))
(assert (not (forall ((xs list)) (= (takeWhile lam xs) xs))))
(check-sat)
