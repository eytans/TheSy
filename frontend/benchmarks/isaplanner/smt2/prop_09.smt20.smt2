(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun |-2| (Nat Nat) Nat)
(declare-fun +2 (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (|-2| Z y) Z)))
(assert (forall ((z Nat)) (= (|-2| (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (|-2| (S z) (S x2)) (|-2| z x2))))
(assert (forall ((y Nat)) (= (+2 Z y) y)))
(assert (forall ((y Nat) (z Nat)) (= (+2 (S z) y) (S (+2 z y)))))
(assert
  (not
    (forall ((i Nat) (j Nat) (k Nat))
      (= (|-2| (|-2| i j) k) (|-2| i (+2 j k))))))
(check-sat)
