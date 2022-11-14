(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((z Nat)) (= (add3acc zero zero z) z)))
(assert
  (forall ((z Nat) (x3 Nat))
    (= (add3acc zero (succ x3) z) (add3acc zero x3 (succ z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (succ x2) y z) (add3acc x2 (succ y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
