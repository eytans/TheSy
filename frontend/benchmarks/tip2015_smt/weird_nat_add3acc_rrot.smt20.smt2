(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun add3acc (Nat Nat Nat) Nat)
(assert (forall ((z Nat)) (= (add3acc zero zero z) z)))
(assert
  (forall ((z Nat) (x3 Nat))
    (= (add3acc zero (succ x3) z) (add3acc zero x3 (succ z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3acc (succ x2) y z) (add3acc x2 (succ y) z))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (add3acc x y z) (add3acc z x y)))))
(check-sat)
