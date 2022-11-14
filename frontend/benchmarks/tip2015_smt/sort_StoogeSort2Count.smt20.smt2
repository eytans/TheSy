(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun sort2 (Int Int) list)
(declare-fun length (list) Int)
(declare-fun splitAt (Int list) pair)
(declare-fun count (Int list) Int)
(declare-fun ++ (list list) list)
(declare-fun stooge2sort2 (list) list)
(declare-fun stoogesort2 (list) list)
(declare-fun stooge2sort1 (list) list)
(assert (= (stoogesort2 nil) nil))
(assert
  (forall ((x Int) (y Int))
    (=> (not (<= x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Int) (y Int))
    (=> (<= x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (div (+ (* 2 (length x)) 1) 3) x) (pair2 ys1 zs))
      (= (stooge2sort2 x) (++ (stoogesort2 ys1) zs)))))
(assert
  (forall ((y Int)) (= (stoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (y2 Int))
    (= (stoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Int) (y2 Int) (x3 Int) (x4 list))
    (= (stoogesort2 (cons y (cons y2 (cons x3 x4))))
      (stooge2sort2
        (stooge2sort1 (stooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (div (length x) 3) x) (pair2 ys1 zs))
      (= (stooge2sort1 x) (++ ys1 (stoogesort2 zs))))))
(assert (= (length nil) 0))
(assert
  (forall ((y Int) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (stoogesort2 xs)) (count x xs)))))
(check-sat)
