(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list ((nil3) (cons3 (head3 sk) (tail3 list))))
(declare-datatype
  list3 ((nil2) (cons2 (head2 list) (tail2 list3))))
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun select2 (sk list2) list2)
(declare-fun select22 (list) list2)
(declare-fun formula (list2) list3)
(declare-fun count (sk list) Nat)
(declare-fun all (fun13 list3) Bool)
(declare-fun all2 (fun12 list) Bool)
(declare-fun lam (list sk) fun13)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(declare-fun apply13 (fun13 list) Bool)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (select22 nil3) nil))
(assert (= (formula nil) nil2))
(assert (forall ((x sk)) (= (select2 x nil) nil)))
(assert
  (forall ((x sk) (x2 list2) (y2 sk) (ys list))
    (= (select2 x (cons (pair2 y2 ys) x2))
      (cons (pair2 y2 (cons3 x ys)) (select2 x x2)))))
(assert
  (forall ((y sk) (xs list))
    (= (select22 (cons3 y xs))
      (cons (pair2 y xs) (select2 y (select22 xs))))))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert
  (forall ((z list2) (y2 sk) (ys list))
    (= (formula (cons (pair2 y2 ys) z))
      (cons2 (cons3 y2 ys) (formula z)))))
(assert (forall ((x sk)) (= (count x nil3) zero)))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (= x z)
      (= (count x (cons3 z ys)) (plus (succ zero) (count x ys))))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (distinct x z) (= (count x (cons3 z ys)) (count x ys)))))
(assert (forall ((q fun12)) (all2 q nil3)))
(assert
  (forall ((q fun12) (y sk) (xs list))
    (= (all2 q (cons3 y xs)) (and (apply12 q y) (all2 q xs)))))
(assert (forall ((q fun13)) (all q nil2)))
(assert
  (forall ((q fun13) (y list) (xs list3))
    (= (all q (cons2 y xs)) (and (apply13 q y) (all q xs)))))
(assert
  (forall ((xs list) (z sk) (x list))
    (= (apply13 (lam xs z) x) (= (count z xs) (count z x)))))
(assert
  (not
    (forall ((xs list) (z sk))
      (all (lam xs z) (formula (select22 xs))))))
(check-sat)
