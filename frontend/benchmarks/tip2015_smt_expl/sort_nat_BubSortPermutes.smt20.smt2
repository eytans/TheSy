(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 Bool) (proj2-pair2 list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun bubble (list) pair3)
(declare-fun bubsort (list) list)
(declare-fun elem (sk list2) Bool)
(declare-fun deleteBy (fun12 sk list2) list2)
(declare-fun isPermutation (list2 list2) Bool)
(declare-fun lam (sk) fun14)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun14)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (isPermutation nil2 nil2))
(assert (= (bubble nil) (pair22 false nil)))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((x sk)) (not (elem x nil2))))
(assert
  (forall ((x sk) (z sk) (xs list2))
    (= (elem x (cons2 z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((x fun12) (y sk)) (= (deleteBy x y nil2) nil2)))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list2))
    (=> (apply14 (apply12 x y) y2)
      (= (deleteBy x y (cons2 y2 ys)) ys))))
(assert
  (forall ((x fun12) (y sk) (y2 sk) (ys list2))
    (=> (not (apply14 (apply12 x y) y2))
      (= (deleteBy x y (cons2 y2 ys)) (cons2 y2 (deleteBy x y ys))))))
(assert
  (forall ((y list2) (x3 sk) (xs list2))
    (= (isPermutation (cons2 x3 xs) y)
      (and (elem x3 y) (isPermutation xs (deleteBy lam2 x3 y))))))
(assert
  (forall ((z sk) (x2 list2))
    (not (isPermutation nil2 (cons2 z x2)))))
(assert
  (forall ((y Nat))
    (= (bubble (cons y nil)) (pair22 false (cons y nil)))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (b12 Bool) (ys12 list))
    (=> (leq y y2)
      (=> (= (bubble (cons y2 xs)) (pair22 b12 ys12))
        (= (bubble (cons y (cons y2 xs))) (pair22 b12 (cons y ys12)))))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (b1 Bool) (ys1 list))
    (=> (not (leq y y2))
      (=> (= (bubble (cons y xs)) (pair22 b1 ys1))
        (= (bubble (cons y (cons y2 xs))) (pair22 true (cons y2 ys1)))))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair22 false ys1)) (= (bubsort x) x))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair22 true ys1))
      (= (bubsort x) (bubsort ys1)))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply14 (lam x4) x5) (= x4 x5))))