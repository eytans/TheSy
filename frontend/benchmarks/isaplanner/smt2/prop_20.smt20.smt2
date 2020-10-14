(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun len (list) Nat)
(declare-fun <=2 (Nat Nat) Bool)
(declare-fun insort (Nat list) list)
(declare-fun sort (list) list)
(assert (= (sort nil) nil))
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
(assert (= (len nil) Z))
(assert
  (forall ((y Nat) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (not (forall ((xs list)) (= (len (sort xs)) (len xs)))))
(check-sat)
