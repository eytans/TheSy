(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun twoThirds (Int) Int)
(declare-fun third (Int) Int)
(declare-fun sort2 (Int Int) list)
(declare-fun ordered (list) Bool)
(declare-fun length (list) Int)
(declare-fun splitAt (Int list) pair)
(declare-fun ++ (list list) list)
(declare-fun nstooge2sort2 (list) list)
(declare-fun nstoogesort2 (list) list)
(declare-fun nstooge2sort1 (list) list)
(assert (ordered nil))
(assert (= (nstoogesort2 nil) nil))
(assert
  (forall ((x Int))
    (=> (distinct x 2)
      (=> (distinct x 1)
        (=> (distinct x 0) (= (twoThirds x) (+ 2 (twoThirds (- x 3)))))))))
(assert
  (forall ((x Int))
    (=> (distinct x 2)
      (=> (distinct x 1) (=> (= x 0) (= (twoThirds x) 0))))))
(assert
  (forall ((x Int))
    (=> (distinct x 2) (=> (= x 1) (= (twoThirds x) 1)))))
(assert (forall ((x Int)) (=> (= x 2) (= (twoThirds x) 1))))
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
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (twoThirds (length x)) x) (pair2 ys1 zs))
      (= (nstooge2sort2 x) (++ (nstoogesort2 ys1) zs)))))
(assert
  (forall ((y Int)) (= (nstoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (y2 Int))
    (= (nstoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Int) (y2 Int) (x3 Int) (x4 list))
    (= (nstoogesort2 (cons y (cons y2 (cons x3 x4))))
      (nstooge2sort2
        (nstooge2sort1 (nstooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (third (length x)) x) (pair2 ys1 zs))
      (= (nstooge2sort1 x) (++ ys1 (nstoogesort2 zs))))))
(assert (= (length nil) 0))
(assert
  (forall ((y Int) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (not (forall ((xs list)) (ordered (nstoogesort2 xs)))))
(check-sat)
