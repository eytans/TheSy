(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun take (Int list) list)
(declare-fun take2 (Int list2) list2)
(declare-fun ordered (list2) Bool)
(declare-fun nmsorttd-half1 (Int) Int)
(declare-fun lmerge (list2 list2) list2)
(declare-fun length (list) Int)
(declare-fun length2 (list2) Int)
(declare-fun drop (Int list) list)
(declare-fun drop2 (Int list2) list2)
(declare-fun nmsorttd (list2) list2)
(assert (ordered nil2))
(assert (= (nmsorttd nil2) nil2))
(assert (forall ((y Int)) (ordered (cons2 y nil2))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (= (ordered (cons2 y (cons2 y2 xs)))
      (and (<= y y2) (ordered (cons2 y2 xs))))))
(assert
  (forall ((x Int))
    (=> (distinct x 1)
      (=> (distinct x 0)
        (= (nmsorttd-half1 x) (+ 1 (nmsorttd-half1 (- x 2))))))))
(assert
  (forall ((x Int))
    (=> (distinct x 1) (=> (= x 0) (= (nmsorttd-half1 x) 0)))))
(assert (forall ((x Int)) (=> (= x 1) (= (nmsorttd-half1 x) 0))))
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
(assert
  (forall ((y Int)) (= (nmsorttd (cons2 y nil2)) (cons2 y nil2))))
(assert
  (forall ((y Int) (x2 Int) (x3 list2) (k Int))
    (=> (= k (nmsorttd-half1 (length2 (cons2 y (cons2 x2 x3)))))
      (= (nmsorttd (cons2 y (cons2 x2 x3)))
        (lmerge (nmsorttd (take2 k (cons2 y (cons2 x2 x3))))
          (nmsorttd (drop2 k (cons2 y (cons2 x2 x3)))))))))
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
