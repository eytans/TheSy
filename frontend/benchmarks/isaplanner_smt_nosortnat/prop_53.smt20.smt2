(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun == (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(declare-fun <=2 (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(assert (== Z Z))
(assert (= (sort nil) nil))
(assert (forall ((z Nat)) (not (== Z (S z)))))
(assert (forall ((x2 Nat)) (not (== (S x2) Z))))
(assert
  (forall ((x2 Nat) (y2 Nat)) (= (== (S x2) (S y2)) (== x2 y2))))
(assert (forall ((x Nat)) (= (count x nil) Z)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (not (== x z)) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (== x z) (= (count x (cons z ys)) (S (count x ys))))))
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert (forall ((x Nat)) (= (insort x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (<=2 x z))
      (= (insort x (cons z xs)) (cons z (insort x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (<=2 x z) (= (insort x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((y Nat) (xs list))
    (= (sort (cons y xs)) (insort y (sort xs)))))
