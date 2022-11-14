(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun third (Int) Int)
(declare-fun sort2 (Int Int) list)
(declare-fun ordered (list) Bool)
(declare-fun length (list) Int)
(declare-fun splitAt (Int list) pair)
(declare-fun ++ (list list) list)
(declare-fun reverse (list) list)
(declare-fun nstooge1sort2 (list) list)
(declare-fun nstoogesort (list) list)
(declare-fun nstooge1sort1 (list) list)
(assert (ordered nil))
(assert (= (nstoogesort nil) nil))
(assert
  (forall ((x Int))
    (=> (distinct x 2)
      (=> (distinct x 1)
        (=> (distinct x 0) (= (third x) (+ 1 (third (- x 3)))))))))
(assert
  (forall ((x Int))
    (=> (distinct x 2)
      (=> (distinct x 1) (=> (= x 0) (= (third x) 0))))))
(assert
  (forall ((x Int))
    (=> (distinct x 2) (=> (= x 1) (= (third x) 0)))))
(assert (forall ((x Int)) (=> (= x 2) (= (third x) 0))))
(assert
  (forall ((x Int) (y Int))
    (=> (not (<= x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Int) (y Int))
    (=> (<= x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert (forall ((y Int)) (ordered (cons y nil))))
(assert
  (forall ((y Int) (y2 Int) (xs list))
    (= (ordered (cons y (cons y2 xs)))
      (and (<= y y2) (ordered (cons y2 xs))))))
(assert
  (forall ((x list) (ys1 list) (zs1 list))
    (=> (= (splitAt (third (length x)) (reverse x)) (pair2 ys1 zs1))
      (= (nstooge1sort2 x) (++ (nstoogesort zs1) (reverse ys1))))))
(assert
  (forall ((y Int)) (= (nstoogesort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (y2 Int))
    (= (nstoogesort (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Int) (y2 Int) (x3 Int) (x4 list))
    (= (nstoogesort (cons y (cons y2 (cons x3 x4))))
      (nstooge1sort2
        (nstooge1sort1 (nstooge1sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (third (length x)) x) (pair2 ys1 zs))
      (= (nstooge1sort1 x) (++ ys1 (nstoogesort zs))))))
(assert (= (length nil) 0))
(assert
  (forall ((y Int) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (= (reverse nil) nil))
(assert
  (forall ((y Int) (xs list))
    (= (reverse (cons y xs)) (++ (reverse xs) (cons y nil)))))
(assert (not (forall ((xs list)) (ordered (nstoogesort xs)))))
(check-sat)
