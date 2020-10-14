(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun == (Nat Nat) Bool)
(declare-fun <=2 (Nat Nat) Bool)
(assert (== Z Z))
(assert (forall ((z Nat)) (not (== Z (S z)))))
(assert (forall ((x2 Nat)) (not (== (S x2) Z))))
(assert
  (forall ((x2 Nat) (y2 Nat)) (= (== (S x2) (S y2)) (== x2 y2))))
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert (not (forall ((n Nat)) (= (<=2 n Z) (== n Z)))))
(check-sat)
