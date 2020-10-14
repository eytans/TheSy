(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun max (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (max Z y) y)))
(assert (forall ((z Nat)) (= (max (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (max (S z) (S x2)) (S (max z x2)))))
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat))
      (= (max (max a b) c) (max a (max b c))))))
(check-sat)
