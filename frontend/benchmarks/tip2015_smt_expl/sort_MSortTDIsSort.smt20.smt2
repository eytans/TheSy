(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun take (Int list) list)
(declare-fun take2 (Int list2) list2)
(declare-fun lmerge (list2 list2) list2)
(declare-fun length (list) Int)
(declare-fun length2 (list2) Int)
(declare-fun insert2 (Int list2) list2)
(declare-fun isort (list2) list2)
(declare-fun drop (Int list) list)
(declare-fun drop2 (Int list2) list2)
(declare-fun msorttd (list2) list2)
(assert (= (isort nil2) nil2))
(assert (= (msorttd nil2) nil2))
(assert (forall ((y list2)) (= (lmerge nil2 y) y)))
(assert
  (forall ((z Int) (x2 list2))
    (= (lmerge (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (not (<= z x3))
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 x3 (lmerge (cons2 z x2) x4))))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (<= z x3)
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 z (lmerge x2 (cons2 x3 x4)))))))
(assert (forall ((x Int)) (= (insert2 x nil2) (cons2 x nil2))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (not (<= x z))
      (= (insert2 x (cons2 z xs)) (cons2 z (insert2 x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (<= x z) (= (insert2 x (cons2 z xs)) (cons2 x (cons2 z xs))))))
(assert
  (forall ((y Int) (xs list2))
    (= (isort (cons2 y xs)) (insert2 y (isort xs)))))
(assert
  (forall ((y Int)) (= (msorttd (cons2 y nil2)) (cons2 y nil2))))
(assert
  (forall ((y Int) (x2 Int) (x3 list2) (k Int))
    (=> (= k (div (length2 (cons2 y (cons2 x2 x3))) 2))
      (= (msorttd (cons2 y (cons2 x2 x3)))
        (lmerge (msorttd (take2 k (cons2 y (cons2 x2 x3))))
          (msorttd (drop2 k (cons2 y (cons2 x2 x3)))))))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (take x nil) nil))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (take2 x nil2) nil2))))
(assert
  (forall ((x Int) (y list)) (=> (<= x 0) (= (take x y) nil))))
(assert
  (forall ((x Int) (y list2)) (=> (<= x 0) (= (take2 x y) nil2))))
(assert
  (forall ((x Int) (z sk) (xs list))
    (=> (not (<= x 0))
      (= (take x (cons z xs)) (cons z (take (- x 1) xs))))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (not (<= x 0))
      (= (take2 x (cons2 z xs)) (cons2 z (take2 (- x 1) xs))))))
(assert (= (length nil) 0))
(assert (= (length2 nil2) 0))
(assert
  (forall ((y sk) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert
  (forall ((y Int) (l list2))
    (= (length2 (cons2 y l)) (+ 1 (length2 l)))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (drop x nil) nil))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (drop2 x nil2) nil2))))
(assert (forall ((x Int) (y list)) (=> (<= x 0) (= (drop x y) y))))
(assert
  (forall ((x Int) (y list2)) (=> (<= x 0) (= (drop2 x y) y))))
(assert
  (forall ((x Int) (z sk) (xs1 list))
    (=> (not (<= x 0)) (= (drop x (cons z xs1)) (drop (- x 1) xs1)))))
(assert
  (forall ((x Int) (z Int) (xs1 list2))
    (=> (not (<= x 0))
      (= (drop2 x (cons2 z xs1)) (drop2 (- x 1) xs1)))))
