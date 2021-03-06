(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun len (list2) Nat)
(declare-fun == (Nat Nat) Bool)
(declare-fun delete (Nat list) list)
(declare-fun <=2 (Nat Nat) Bool)
(assert (== Z Z))
(assert (forall ((z Nat)) (not (== Z (S z)))))
(assert (forall ((x2 Nat)) (not (== (S x2) Z))))
(assert
  (forall ((x2 Nat) (y2 Nat)) (= (== (S x2) (S y2)) (== x2 y2))))
(assert (forall ((x Nat)) (= (delete x nil) nil)))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (== x z))
      (= (delete x (cons z xs)) (cons z (delete x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (== x z) (= (delete x (cons z xs)) (delete x xs)))))
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert (= (len nil2) Z))
(assert
  (forall ((y sk) (xs list2)) (= (len (cons2 y xs)) (S (len xs)))))
