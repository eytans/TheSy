(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun interleave (list list) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(assert (forall ((y list)) (= (interleave nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (interleave (cons z xs) y) (cons z (interleave y xs)))))
(assert (= (evens nil) nil))
(assert
  (forall ((y sk) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert (= (odds nil) nil))
(assert
  (forall ((y sk) (xs list)) (= (odds (cons y xs)) (evens xs))))
