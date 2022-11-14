(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun ++ (list list) list)
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((xs list) (ys list) (zs list))
      (=> (= (++ xs zs) (++ ys zs)) (= xs ys)))))
(check-sat)
