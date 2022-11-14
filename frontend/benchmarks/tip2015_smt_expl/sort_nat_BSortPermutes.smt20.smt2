(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(declare-fun evens (list) list)
(declare-fun evens2 (list2) list2)
(declare-fun odds (list) list)
(declare-fun odds2 (list2) list2)
(declare-fun elem (sk list2) Bool)
(declare-fun deleteBy (fun12 sk list2) list2)
(declare-fun isPermutation (list2 list2) Bool)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun lam (sk) fun14)
(declare-const lam2 fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) fun14)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk) Bool)
(declare-fun apply15 (fun15 sk2) sk)
(declare-fun apply16 (fun16 sk2) sk2)
(assert (isPermutation nil2 nil2))
(assert (= (bsort nil) nil))
(assert (= (evens nil) nil))
(assert (= (evens2 nil2) nil2))
(assert (= (odds nil) nil))
(assert (= (odds2 nil2) nil2))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (leq x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (not (leq x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((y Nat) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert
  (forall ((y sk) (xs list2))
    (= (evens2 (cons2 y xs)) (cons2 y (odds2 xs)))))
(assert
  (forall ((y Nat) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert
  (forall ((y sk) (xs list2)) (= (odds2 (cons2 y xs)) (evens2 xs))))
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
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert (forall ((y list)) (= (pairs nil y) y)))
(assert
  (forall ((z Nat) (x2 list))
    (= (pairs (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x2 list) (x3 Nat) (x4 list))
    (= (pairs (cons z x2) (cons x3 x4))
      (++ (sort2 z x3) (pairs x2 x4)))))
(assert (forall ((y list)) (= (stitch nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (stitch (cons z xs) y) (cons z (pairs xs y)))))
(assert (forall ((y list)) (= (bmerge nil y) nil)))
(assert
  (forall ((z Nat) (x2 list))
    (= (bmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x3 Nat) (x4 list) (fail list) (x7 Nat) (x8 list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z (cons x7 x8))) (evens (cons x3 x4)))
          (bmerge (odds (cons z (cons x7 x8))) (odds (cons x3 x4)))))
      (= (bmerge (cons z (cons x7 x8)) (cons x3 x4)) fail))))
(assert
  (forall ((z Nat) (x3 Nat) (fail list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z nil)) (evens (cons x3 nil)))
          (bmerge (odds (cons z nil)) (odds (cons x3 nil)))))
      (= (bmerge (cons z nil) (cons x3 nil)) (sort2 z x3)))))
(assert
  (forall ((z Nat) (x3 Nat) (fail list) (x5 Nat) (x6 list))
    (=>
      (= fail
        (stitch
          (bmerge (evens (cons z nil)) (evens (cons x3 (cons x5 x6))))
          (bmerge (odds (cons z nil)) (odds (cons x3 (cons x5 x6))))))
      (= (bmerge (cons z nil) (cons x3 (cons x5 x6))) fail))))
(assert (forall ((y Nat)) (= (bsort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (bsort (cons y (cons x2 x3)))
      (bmerge (bsort (evens (cons y (cons x2 x3))))
        (bsort (odds (cons y (cons x2 x3))))))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply14 (lam x4) x5) (= x4 x5))))
