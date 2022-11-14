(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(declare-fun isPermutation (list list) Bool)
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
(assert (isPermutation nil nil))
(assert
  (forall ((z Int) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (not (forall ((xs list)) (isPermutation (isort xs) xs))))
(check-sat)
