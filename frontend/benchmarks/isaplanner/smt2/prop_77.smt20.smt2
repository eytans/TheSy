(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun <=2 (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun && (Bool Bool) Bool)
(declare-fun sorted (list) Bool)
(assert (sorted nil))
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
(assert (forall ((y Bool)) (not (&& false y))))
(assert (forall ((y Bool)) (= (&& true y) y)))
(assert (forall ((y Nat)) (sorted (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat) (ys list))
    (= (sorted (cons y (cons y2 ys)))
      (&& (<=2 y y2) (sorted (cons y2 ys))))))
(assert
  (not
    (forall ((x Nat) (xs list))
      (=> (sorted xs) (sorted (insort x xs))))))
(check-sat)
