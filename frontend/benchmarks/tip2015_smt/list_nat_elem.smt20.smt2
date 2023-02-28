(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-const undefined sk)
(declare-fun elem (sk list) Bool)
(declare-fun at (list Nat) sk)
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((y Nat)) (= (at nil y) undefined)))
(assert (forall ((z sk) (x2 list)) (= (at (cons z x2) zero) z)))
(assert
  (forall ((z sk) (x2 list) (x3 Nat))
    (= (at (cons z x2) (succ x3)) (at x2 x3))))
(assert
  (not
    (forall ((x sk) (xs list))
      (=> (elem x xs) (exists ((y Nat)) (= x (at xs y)))))))
(check-sat)