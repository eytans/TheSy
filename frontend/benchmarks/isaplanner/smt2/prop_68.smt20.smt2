(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun len (list) Nat)
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
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert
  (not
    (forall ((n Nat) (xs list)) (<=2 (len (delete n xs)) (len xs)))))
(check-sat)
