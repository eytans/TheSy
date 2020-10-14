(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun last (list) Nat)
(declare-fun butlast (list) list)
(declare-fun ++ (list list) list)
(assert (= (last nil) Z))
(assert (forall ((y Nat)) (= (last (cons y nil)) y)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (last (cons y (cons x2 x3))) (last (cons x2 x3)))))
(assert (= (butlast nil) nil))
(assert (forall ((y Nat)) (= (butlast (cons y nil)) nil)))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (butlast (cons y (cons x2 x3)))
      (cons y (butlast (cons x2 x3))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((xs list))
      (=> (is-cons xs) (= (++ (butlast xs) (cons (last xs) nil)) xs)))))
(check-sat)
