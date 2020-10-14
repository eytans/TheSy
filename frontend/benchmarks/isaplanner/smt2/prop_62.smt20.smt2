(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun last (list) Nat)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert
  (not
    (forall ((xs list) (x Nat))
      (=> (is-cons xs) (= (last (cons x xs)) (last xs))))))
(check-sat)
