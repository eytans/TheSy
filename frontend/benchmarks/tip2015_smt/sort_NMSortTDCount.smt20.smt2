(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun take (Int list) list)
(declare-fun nmsorttd-half1 (Int) Int)
(declare-fun lmerge (list list) list)
(declare-fun length (list) Int)
(declare-fun drop (Int list) list)
(declare-fun nmsorttd (list) list)
(declare-fun count (Int list) Int)
(assert (= (nmsorttd nil) nil))
(assert
  (forall ((x Int))
    (=> (distinct x 1)
      (=> (distinct x 0)
        (= (nmsorttd-half1 x) (+ 1 (nmsorttd-half1 (- x 2))))))))
(assert
  (forall ((x Int))
    (=> (distinct x 1) (=> (= x 0) (= (nmsorttd-half1 x) 0)))))
(assert (forall ((x Int)) (=> (= x 1) (= (nmsorttd-half1 x) 0))))
(assert (forall ((y list)) (= (lmerge nil y) y)))
(assert
  (forall ((z Int) (x2 list))
    (= (lmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Int) (x2 list) (x3 Int) (x4 list))
    (=> (not (<= z x3))
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons x3 (lmerge (cons z x2) x4))))))
(assert
  (forall ((z Int) (x2 list) (x3 Int) (x4 list))
    (=> (<= z x3)
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons z (lmerge x2 (cons x3 x4)))))))
(assert
  (forall ((y Int)) (= (nmsorttd (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (x2 Int) (x3 list) (k Int))
    (=> (= k (nmsorttd-half1 (length (cons y (cons x2 x3)))))
      (= (nmsorttd (cons y (cons x2 x3)))
        (lmerge (nmsorttd (take k (cons y (cons x2 x3))))
          (nmsorttd (drop k (cons y (cons x2 x3)))))))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (take x nil) nil))))
(assert
  (forall ((x Int) (y list)) (=> (<= x 0) (= (take x y) nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (not (<= x 0))
      (= (take x (cons z xs)) (cons z (take (- x 1) xs))))))
(assert (= (length nil) 0))
(assert
  (forall ((y Int) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (drop x nil) nil))))
(assert (forall ((x Int) (y list)) (=> (<= x 0) (= (drop x y) y))))
(assert
  (forall ((x Int) (z Int) (xs1 list))
    (=> (not (<= x 0)) (= (drop x (cons z xs1)) (drop (- x 1) xs1)))))
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
      (= (count x (nmsorttd xs)) (count x xs)))))
(check-sat)
