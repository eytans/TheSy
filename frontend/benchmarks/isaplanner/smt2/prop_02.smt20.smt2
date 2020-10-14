(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun == (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(declare-fun +2 (Nat Nat) Nat)
(declare-fun ++ (list list) list)
(assert (== Z Z))
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
(assert (forall ((y Nat)) (= (+2 Z y) y)))
(assert (forall ((y Nat) (z Nat)) (= (+2 (S z) y) (S (+2 z y)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((n Nat) (xs list) (ys list))
      (= (+2 (count n xs) (count n ys)) (count n (++ xs ys))))))
(check-sat)
