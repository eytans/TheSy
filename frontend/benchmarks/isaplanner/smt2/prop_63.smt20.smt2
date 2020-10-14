(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun len (list) Nat)
(declare-fun last (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun <2 (Nat Nat) Bool)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (forall ((x Nat)) (not (<2 x Z))))
(assert (forall ((z Nat)) (<2 Z (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<2 (S x2) (S z)) (<2 x2 z))))
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 Nat) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (=> (<2 n (len xs)) (= (last (drop n xs)) (last xs))))))
(check-sat)
