(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun last (list) Nat)
(declare-fun lastOfTwo (list list) Nat)
(declare-fun ++ (list list) list)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (forall ((x list)) (= (lastOfTwo x nil) (last x))))
(assert
  (forall ((x list) (z Nat) (x2 list))
    (= (lastOfTwo x (cons z x2)) (last (cons z x2)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((xs list) (ys list))
      (= (last (++ xs ys)) (lastOfTwo xs ys)))))
(check-sat)
