(declare-sort fun1 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun leq (Nat Nat) Bool)
(declare-fun gt (Nat Nat) Bool)
(declare-fun qsort (list) list)
(declare-fun filter (fun1 list) list)
(declare-fun count (Nat list) Nat)
(declare-fun ++ (list list) list)
(declare-fun lam (Nat) fun1)
(declare-fun lam2 (Nat) fun1)
(declare-fun apply1 (fun1 Nat) Bool)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (qsort nil) nil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((x Nat) (y Nat)) (= (gt x y) (lt y x))))
(assert (forall ((q fun1)) (= (filter q nil) nil)))
(assert
  (forall ((q fun1) (y Nat) (xs list))
    (=> (apply1 q y)
      (= (filter q (cons y xs)) (cons y (filter q xs))))))
(assert
  (forall ((q fun1) (y Nat) (xs list))
    (=> (not (apply1 q y)) (= (filter q (cons y xs)) (filter q xs)))))
(assert (forall ((x Nat)) (= (count x nil) zero)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= x z)
      (= (count x (cons z ys)) (plus (succ zero) (count x ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y Nat) (xs list))
    (= (qsort (cons y xs))
      (++ (qsort (filter (lam y) xs))
        (++ (cons y nil) (qsort (filter (lam2 y) xs)))))))
(assert
  (forall ((y Nat) (z Nat)) (= (apply1 (lam y) z) (leq z y))))
(assert
  (forall ((y Nat) (x2 Nat)) (= (apply1 (lam2 y) x2) (gt x2 y))))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (qsort xs)) (count x xs)))))
(check-sat)
