(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun ++ (list list) list)
(declare-fun rotate (Nat list) list)
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y list)) (= (rotate zero y) y)))
(assert (forall ((z Nat)) (= (rotate (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list))
    (= (rotate (succ z) (cons z2 xs1))
      (rotate z (++ xs1 (cons z2 nil))))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n (++ xs xs)) (++ (rotate n xs) (rotate n xs))))))
(check-sat)
