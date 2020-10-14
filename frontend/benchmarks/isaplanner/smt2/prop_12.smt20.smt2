(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun map2 (fun1 list) list)
(declare-fun drop (Nat list) list)
(declare-fun apply1 (fun1 sk) sk)
(assert (forall ((x fun1)) (= (map2 x nil) nil)))
(assert
  (forall ((x fun1) (z sk) (xs list))
    (= (map2 x (cons z xs)) (cons (apply1 x z) (map2 x xs)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert
  (not
    (forall ((n Nat) (f fun1) (xs list))
      (= (drop n (map2 f xs)) (map2 f (drop n xs))))))
(check-sat)
