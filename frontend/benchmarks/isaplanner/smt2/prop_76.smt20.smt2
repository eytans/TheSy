(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun == (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
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
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((n Nat) (m Nat) (xs list))
      (=> (not (== n m))
        (= (count n (++ xs (cons m nil))) (count n xs))))))
(check-sat)
