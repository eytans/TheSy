(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun filter (fun13 list) list)
(declare-fun nubBy (fun12 list) list)
(declare-fun elem (sk list) Bool)
(declare-fun lam (fun12 sk) fun13)
(declare-fun lam2 (sk) fun13)
(declare-const lam3 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
(assert (forall ((p fun13)) (= (filter p nil) nil)))
(assert
  (forall ((p fun13) (y sk) (xs list))
    (=> (apply13 p y)
      (= (filter p (cons y xs)) (cons y (filter p xs))))))
(assert
  (forall ((p fun13) (y sk) (xs list))
    (=> (not (apply13 p y)) (= (filter p (cons y xs)) (filter p xs)))))
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
    (= (apply13 (lam x z) y2) (not (apply13 (apply12 x z) y2)))))
(assert (forall ((y sk)) (= (apply12 lam3 y) (lam2 y))))
(assert (forall ((y sk) (z sk)) (= (apply13 (lam2 y) z) (= y z))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (elem x (nubBy lam3 xs))))))
(check-sat)
