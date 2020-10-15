(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun min (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (min Z y) Z)))
(assert (forall ((z Nat)) (= (min (S z) Z) Z)))
(assert
  (forall ((z Nat) (y1 Nat)) (= (min (S z) (S y1)) (S (min z y1)))))
