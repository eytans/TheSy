(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun lmerge (list2 list2) list2)
(declare-fun msorttd (list2) list2)
(declare-fun take (Int list) list)
(declare-fun take2 (Int list2) list2)
(declare-fun length (list) Int)
(declare-fun length2 (list2) Int)
(declare-fun elem (sk list) Bool)
(declare-fun drop (Int list) list)
(declare-fun drop2 (Int list2) list2)
(declare-fun deleteBy (fun12 sk list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun lam (sk) fun14)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun14)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (isPermutation nil nil))
(assert (= (msorttd nil2) nil2))
(assert (= (length nil) 0))
(assert (= (length2 nil2) 0))
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
  (forall ((y sk) (l list))
    (= (length (cons y l)) (+ 1 (length l)))))
(assert
  (forall ((y Int) (l list2))
    (= (length2 (cons2 y l)) (+ 1 (length2 l)))))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
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
(assert
  (forall ((y Int)) (= (msorttd (cons2 y nil2)) (cons2 y nil2))))
(assert
  (forall ((y Int) (x2 Int) (x3 list2) (k Int))
    (=> (= k (div (length2 (cons2 y (cons2 x2 x3))) 2))
      (= (msorttd (cons2 y (cons2 x2 x3)))
        (lmerge (msorttd (take2 k (cons2 y (cons2 x2 x3))))
          (msorttd (drop2 k (cons2 y (cons2 x2 x3)))))))))
(assert (forall ((x fun12) (y sk)) (= (deleteBy x y nil) nil)))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (apply14 (apply12 x y) y2)
      (= (deleteBy x y (cons y2 ys)) ys))))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (not (apply14 (apply12 x y) y2))
      (= (deleteBy x y (cons y2 ys)) (cons y2 (deleteBy x y ys))))))
(assert
  (forall ((y list) (x3 sk) (xs list))
    (= (isPermutation (cons x3 xs) y)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y))))))
(assert
  (forall ((z sk) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply14 (lam x4) x5) (= x4 x5))))
