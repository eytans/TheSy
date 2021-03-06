(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun len (list2) Nat)
(declare-fun <2 (Nat Nat) Bool)
(declare-fun ins (Nat list) list)
(assert (forall ((x Nat)) (not (<2 x Z))))
(assert (forall ((z Nat)) (<2 Z (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<2 (S x2) (S z)) (<2 x2 z))))
(assert (forall ((x Nat)) (= (ins x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (<2 x z)) (= (ins x (cons z xs)) (cons z (ins x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (<2 x z) (= (ins x (cons z xs)) (cons x (cons z xs))))))
(assert (= (len nil2) Z))
(assert
  (forall ((y sk) (xs list2)) (= (len (cons2 y xs)) (S (len xs)))))
