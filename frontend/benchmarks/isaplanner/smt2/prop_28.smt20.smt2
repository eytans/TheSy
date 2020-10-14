(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun == (Nat Nat) Bool)
(declare-fun elem (Nat list) Bool)
(declare-fun ++ (list list) list)
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
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not (forall ((x Nat) (xs list)) (elem x (++ xs (cons x nil))))))
(check-sat)
