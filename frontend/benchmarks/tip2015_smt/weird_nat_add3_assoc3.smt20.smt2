(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun add3 (Nat Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((z Nat)) (= (add3 zero zero z) z)))
(assert
  (forall ((z Nat) (x3 Nat))
    (= (add3 zero (succ x3) z) (plus (succ zero) (add3 zero x3 z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3 (succ x2) y z) (plus (succ zero) (add3 x2 y z)))))
(assert
  (not
    (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat))
      (= (add3 x1 (add3 x2 x3 x4) x5) (add3 x1 x2 (add3 x3 x4 x5))))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
