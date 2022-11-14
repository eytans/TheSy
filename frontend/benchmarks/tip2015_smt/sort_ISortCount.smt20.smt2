(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(declare-fun count (Int list) Int)
(assert (= (isort nil) nil))
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
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (isort xs)) (count x xs)))))
(check-sat)
