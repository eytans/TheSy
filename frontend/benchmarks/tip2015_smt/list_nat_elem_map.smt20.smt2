(declare-sort sk 0)
(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun map2 (fun1 list) list)
(declare-fun elem (sk list) Bool)
(declare-fun apply1 (fun1 sk) sk)
(assert (forall ((f fun1)) (= (map2 f nil) nil)))
(assert
  (forall ((f fun1) (y sk) (xs list))
    (= (map2 f (cons y xs)) (cons (apply1 f y) (map2 f xs)))))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert
  (not
    (forall ((y sk) (f fun1) (xs list))
      (=> (elem y (map2 f xs))
        (exists ((x sk)) (and (= (apply1 f x) y) (elem y xs)))))))
(check-sat)
