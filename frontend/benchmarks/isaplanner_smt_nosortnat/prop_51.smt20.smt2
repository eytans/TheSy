(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun butlast (list) list)
(declare-fun ++ (list list) list)
(assert (= (butlast nil) nil))
(assert (forall ((y sk)) (= (butlast (cons y nil)) nil)))
(assert
  (forall ((y sk) (x2 sk) (x3 list))
    (= (butlast (cons y (cons x2 x3)))
      (cons y (butlast (cons x2 x3))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
