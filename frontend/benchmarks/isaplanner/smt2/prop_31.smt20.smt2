(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun min (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (min Z y) Z)))
(assert (forall ((z Nat)) (= (min (S z) Z) Z)))
(assert
  (forall ((z Nat) (y1 Nat)) (= (min (S z) (S y1)) (S (min z y1)))))
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat))
      (= (min (min a b) c) (min a (min b c))))))
(check-sat)
