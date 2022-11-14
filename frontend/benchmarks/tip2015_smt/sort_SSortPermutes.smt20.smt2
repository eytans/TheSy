(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun ssort-minimum1 (Int list) Int)
(declare-fun ssort (list) list)
(declare-fun deleteBy (fun1 Int list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun lam (Int) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Int) fun12)
(declare-fun apply12 (fun12 Int) Bool)
(assert (isPermutation nil nil))
(assert (= (ssort nil) nil))
(assert (forall ((x Int)) (= (ssort-minimum1 x nil) x)))
(assert
  (forall ((x Int) (y1 Int) (ys1 list))
    (=> (not (<= y1 x))
      (= (ssort-minimum1 x (cons y1 ys1)) (ssort-minimum1 x ys1)))))
(assert
  (forall ((x Int) (y1 Int) (ys1 list))
    (=> (<= y1 x)
      (= (ssort-minimum1 x (cons y1 ys1)) (ssort-minimum1 y1 ys1)))))
(assert (forall ((x fun1) (y Int)) (= (deleteBy x y nil) nil)))
(assert
  (forall ((x fun1) (y Int) (y2 Int) (ys list))
    (=> (apply12 (apply1 x y) y2) (= (deleteBy x y (cons y2 ys)) ys))))
(assert
  (forall ((x fun1) (y Int) (y2 Int) (ys list))
    (=> (not (apply12 (apply1 x y) y2))
      (= (deleteBy x y (cons y2 ys)) (cons y2 (deleteBy x y ys))))))
(assert
  (forall ((z Int) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert
  (forall ((y Int) (ys list) (m Int))
    (=> (= m (ssort-minimum1 y ys))
      (= (ssort (cons y ys))
        (cons m (ssort (deleteBy lam2 m (cons y ys))))))))
(assert (forall ((z Int)) (= (apply1 lam2 z) (lam z))))
(assert
  (forall ((z Int) (x2 Int)) (= (apply12 (lam z) x2) (= z x2))))
(assert (not (forall ((xs list)) (isPermutation (ssort xs) xs))))
(check-sat)
