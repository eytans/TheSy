(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun filter (fun12 list) list)
(declare-fun ++ (list list) list)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(assert (forall ((x fun12)) (= (filter x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (apply12 x z)
      (= (filter x (cons z xs)) (cons z (filter x xs))))))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (not (apply12 x z)) (= (filter x (cons z xs)) (filter x xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((p fun12) (xs list) (ys list))
      (= (filter p (++ xs ys)) (++ (filter p xs) (filter p ys))))))
(check-sat)
