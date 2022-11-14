(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun snoc (sk list) list)
(declare-fun rotate (Nat list) list)
(declare-fun ++ (list list) list)
(assert (forall ((x sk)) (= (snoc x nil) (cons x nil))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (= (snoc x (cons z ys)) (cons z (snoc x ys)))))
(assert (forall ((y list)) (= (rotate zero y) y)))
(assert (forall ((z Nat)) (= (rotate (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list))
    (= (rotate (succ z) (cons z2 xs1)) (rotate z (snoc z2 xs1)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n (++ xs xs)) (++ (rotate n xs) (rotate n xs))))))
(check-sat)
