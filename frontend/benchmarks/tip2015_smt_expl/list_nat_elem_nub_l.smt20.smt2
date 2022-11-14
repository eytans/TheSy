(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun filter (fun14 list) list)
(declare-fun nubBy (fun12 list) list)
(declare-fun elem (sk list) Bool)
(declare-fun lam (fun12 sk) fun14)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun14)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (forall ((p fun14)) (= (filter p nil) nil)))
(assert
  (forall ((p fun14) (y sk) (xs list))
    (=> (apply14 p y)
      (= (filter p (cons y xs)) (cons y (filter p xs))))))
(assert
  (forall ((p fun14) (y sk) (xs list))
    (=> (not (apply14 p y)) (= (filter p (cons y xs)) (filter p xs)))))
(assert (forall ((x fun12)) (= (nubBy x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (= (nubBy x (cons z xs))
      (cons z (nubBy x (filter (lam x z) xs))))))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert
  (forall ((x fun12) (z sk) (y2 sk))
    (= (apply14 (lam x z) y2) (not (apply14 (apply12 x z) y2)))))
