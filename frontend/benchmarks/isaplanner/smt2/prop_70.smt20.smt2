(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun <=2 (Nat Nat) Bool)
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert
  (not (forall ((m Nat) (n Nat)) (=> (<=2 m n) (<=2 m (S n))))))
(check-sat)
