(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun deleteBy (fun12 sk list) list)
(declare-fun deleteAll (sk list) list)
(declare-fun count (sk list) Int)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun14)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (forall ((x fun12) (y sk)) (= (deleteBy x y nil) nil)))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (apply14 (apply12 x y) y2)
      (= (deleteBy x y (cons y2 ys)) ys))))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list))
    (=> (not (apply14 (apply12 x y) y2))
      (= (deleteBy x y (cons y2 ys)) (cons y2 (deleteBy x y ys))))))
(assert (forall ((x sk)) (= (deleteAll x nil) nil)))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (= x z) (= (deleteAll x (cons z ys)) (deleteAll x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (distinct x z)
      (= (deleteAll x (cons z ys)) (cons z (deleteAll x ys))))))
(assert (forall ((x sk)) (= (count x nil) 0)))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
