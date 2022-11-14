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
    (forall ((x1 Nat) (x2 Nat) (x3 Nat) (x4 Nat) (x5 Nat))
      (= (add3acc (add3acc x1 x2 x3) x4 x5)
        (add3acc x1 x2 (add3acc x3 x4 x5))))))
(check-sat)
