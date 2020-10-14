(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun min (Nat Nat) Nat)
(declare-fun == (Nat Nat) Bool)
(declare-fun <=2 (Nat Nat) Bool)
(assert (forall ((y Nat)) (= (min Z y) Z)))
(assert (forall ((z Nat)) (= (min (S z) Z) Z)))
(assert
  (forall ((z Nat) (y1 Nat)) (= (min (S z) (S y1)) (S (min z y1)))))
(assert (== Z Z))
(assert (forall ((z Nat)) (not (== Z (S z)))))
(assert (forall ((x2 Nat)) (not (== (S x2) Z))))
(assert
  (forall ((x2 Nat) (y2 Nat)) (= (== (S x2) (S y2)) (== x2 y2))))
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert
  (not (forall ((a Nat) (b Nat)) (= (== (min a b) a) (<=2 a b)))))
(check-sat)
