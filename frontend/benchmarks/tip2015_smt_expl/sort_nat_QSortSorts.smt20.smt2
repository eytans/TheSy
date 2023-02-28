(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun leq (Nat Nat) Bool)
(declare-fun ordered (list) Bool)
(declare-fun gt (Nat Nat) Bool)
(declare-fun qsort (list) list)
(declare-fun filter (fun1 list) list)
(declare-fun filter2 (fun14 list2) list2)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun lam (Nat) fun1)
(declare-fun lam2 (Nat) fun1)
(declare-fun apply1 (fun1 Nat) Bool)
(declare-fun apply12 (fun12 sk) sk)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (ordered nil))
(assert (= (qsort nil) nil))
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y Nat)) (ordered (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (ordered (cons y (cons y2 xs)))
      (and (leq y y2) (ordered (cons y2 xs))))))
(assert (forall ((x Nat) (y Nat)) (= (gt x y) (lt y x))))
(assert (forall ((q fun1)) (= (filter q nil) nil)))
(assert
  (forall ((q fun1) (y Nat) (xs list))
    (=> (apply1 q y)
      (= (filter q (cons y xs)) (cons y (filter q xs))))))
(assert
  (forall ((q fun1) (y Nat) (xs list))
    (=> (not (apply1 q y)) (= (filter q (cons y xs)) (filter q xs)))))
(assert (forall ((q fun14)) (= (filter2 q nil2) nil2)))
(assert
  (forall ((q fun14) (y sk) (xs list2))
    (=> (apply14 q y)
      (= (filter2 q (cons2 y xs)) (cons2 y (filter2 q xs))))))
(assert
  (forall ((q fun14) (y sk) (xs list2))
    (=> (not (apply14 q y))
      (= (filter2 q (cons2 y xs)) (filter2 q xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert
  (forall ((y Nat) (xs list))
    (= (qsort (cons y xs))
      (++ (qsort (filter (lam y) xs))
        (++ (cons y nil) (qsort (filter (lam2 y) xs)))))))
(assert
  (forall ((y Nat) (z Nat)) (= (apply1 (lam y) z) (leq z y))))
(assert
  (forall ((y Nat) (x2 Nat)) (= (apply1 (lam2 y) x2) (gt x2 y))))