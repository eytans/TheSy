(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun == (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun ++ (list2 list2) list2)
(assert (== Z Z))
(assert (forall ((z Nat)) (not (== Z (S z)))))
(assert (forall ((x2 Nat)) (not (== (S x2) Z))))
(assert
  (forall ((x2 Nat) (y2 Nat)) (= (== (S x2) (S y2)) (== x2 y2))))
(assert (forall ((x Nat)) (not (elem x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (== x z)) (= (elem x (cons z xs)) (elem x xs)))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (== x z) (elem x (cons z xs)))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
