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
    (forall ((x Nat) (y Nat) (z Nat))
      (= (add3 x y z) (plus x (plus y z))))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
