(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  pair4 ((pair23 (proj1-pair3 sk) (proj2-pair3 sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 list2) (proj2-pair2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun take (Int list) list)
(declare-fun sort2 (Int Int) list2)
(declare-fun length (list) Int)
(declare-fun length2 (list2) Int)
(declare-fun drop (Int list) list)
(declare-fun splitAt (Int list) pair)
(declare-fun splitAt2 (Int list2) pair3)
(declare-fun count (sk list) Int)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun reverse (list) list)
(declare-fun reverse2 (list2) list2)
(declare-fun stooge1sort2 (list2) list2)
(declare-fun stoogesort (list2) list2)
(declare-fun stooge1sort1 (list2) list2)
(assert (= (stoogesort nil2) nil2))
(assert
  (forall ((x Int) (y Int))
    (=> (not (<= x y)) (= (sort2 x y) (cons2 y (cons2 x nil2))))))
(assert
  (forall ((x Int) (y Int))
    (=> (<= x y) (= (sort2 x y) (cons2 x (cons2 y nil2))))))
(assert
  (forall ((x list2) (ys1 list2) (zs1 list2))
    (=>
      (= (splitAt2 (div (length2 x) 3) (reverse2 x)) (pair22 ys1 zs1))
      (= (stooge1sort2 x) (++2 (stoogesort zs1) (reverse2 ys1))))))
(assert
  (forall ((y Int)) (= (stoogesort (cons2 y nil2)) (cons2 y nil2))))
(assert
  (forall ((y Int) (y2 Int))
    (= (stoogesort (cons2 y (cons2 y2 nil2))) (sort2 y y2))))
(assert
  (forall ((y Int) (y2 Int) (x3 Int) (x4 list2))
    (= (stoogesort (cons2 y (cons2 y2 (cons2 x3 x4))))
      (stooge1sort2
        (stooge1sort1
          (stooge1sort2 (cons2 y (cons2 y2 (cons2 x3 x4)))))))))
(assert
  (forall ((x list2) (ys1 list2) (zs list2))
    (=> (= (splitAt2 (div (length2 x) 3) x) (pair22 ys1 zs))
      (= (stooge1sort1 x) (++2 ys1 (stoogesort zs))))))
(assert
  (forall ((x Int)) (=> (not (<= x 0)) (= (take x nil) nil))))
(assert
  (forall ((x Int) (y list)) (=> (<= x 0) (= (take x y) nil))))
(assert
  (forall ((x Int) (z sk) (xs list))
    (=> (not (<= x 0))
      (= (take x (cons z xs)) (cons z (take (- x 1) xs))))))
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
(assert (forall ((x Int) (y list)) (=> (<= x 0) (= (drop x y) y))))
(assert
  (forall ((x Int) (z sk) (xs1 list))
    (=> (not (<= x 0)) (= (drop x (cons z xs1)) (drop (- x 1) xs1)))))
(assert
  (forall ((x Int) (y list))
    (= (splitAt x y) (pair2 (take x y) (drop x y)))))
(assert (forall ((x sk)) (= (count x nil) 0)))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y list2) (z Int) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert (= (reverse nil) nil))
(assert (= (reverse2 nil2) nil2))
(assert
  (forall ((y sk) (xs list))
    (= (reverse (cons y xs)) (++ (reverse xs) (cons y nil)))))
(assert
  (forall ((y Int) (xs list2))
    (= (reverse2 (cons2 y xs)) (++2 (reverse2 xs) (cons2 y nil2)))))
