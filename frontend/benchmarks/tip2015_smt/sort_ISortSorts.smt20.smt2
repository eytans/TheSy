(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun ordered (list) Bool)
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(assert (ordered nil))
(assert (= (isort nil) nil))
(assert (forall ((y Int)) (ordered (cons y nil))))
(assert
  (forall ((y Int) (y2 Int) (xs list))
    (= (ordered (cons y (cons y2 xs)))
      (and (<= y y2) (ordered (cons y2 xs))))))
(assert (forall ((x Int)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (not (<= x z))
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (<= x z) (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((y Int) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
(assert (not (forall ((xs list)) (ordered (isort xs)))))
(check-sat)
