(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun elem (sk list) Bool)
(declare-fun deleteBy (fun12 sk list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun lam (sk) fun13)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun13)
(declare-fun apply13 (fun13 sk) Bool)
(assert (isPermutation nil nil))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((x fun12) (y sk)) (= (deleteBy x y nil) nil)))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (apply13 (apply12 x y) y2)
      (= (deleteBy x y (cons y2 ys)) ys))))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (not (apply13 (apply12 x y) y2))
      (= (deleteBy x y (cons y2 ys)) (cons y2 (deleteBy x y ys))))))
(assert
  (forall ((y list) (x3 sk) (xs list))
    (= (isPermutation (cons x3 xs) y)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y))))))
(assert
  (forall ((z sk) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply13 (lam x4) x5) (= x4 x5))))
(assert
  (not
    (forall ((xs list) (ys list))
      (=> (isPermutation xs ys) (isPermutation ys xs)))))
(check-sat)
