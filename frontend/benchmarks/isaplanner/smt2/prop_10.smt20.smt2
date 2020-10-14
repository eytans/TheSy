(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun |-2| (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (|-2| Z y) Z)))
(assert (forall ((z Nat)) (= (|-2| (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (|-2| (S z) (S x2)) (|-2| z x2))))
(assert (not (forall ((m Nat)) (= (|-2| m m) Z))))
(check-sat)
