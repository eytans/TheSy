(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun take (Nat list) list)
(declare-fun map2 (fun1 list) list)
(declare-fun apply1 (fun1 sk) sk)
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert (forall ((x fun1)) (= (map2 x nil) nil)))
(assert
  (forall ((x fun1) (z sk) (xs list))
    (= (map2 x (cons z xs)) (cons (apply1 x z) (map2 x xs)))))
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list))
      (= (take n (map2 f xs)) (map2 f (take n xs))))))
(check-sat)
