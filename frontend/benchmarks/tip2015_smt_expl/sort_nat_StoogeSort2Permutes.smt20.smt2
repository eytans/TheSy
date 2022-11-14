(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype
  pair4 ((pair23 (proj1-pair3 sk) (proj2-pair3 sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 list2) (proj2-pair2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun times (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun leq (Nat Nat) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun idiv (Nat Nat) Nat)
(declare-fun stooge2sort2 (list) list)
(declare-fun stoogesort2 (list) list)
(declare-fun stooge2sort1 (list) list)
(declare-fun take (Nat list2) list2)
(declare-fun length (list) Nat)
(declare-fun length2 (list2) Nat)
(declare-fun elem (sk list2) Bool)
(declare-fun drop (Nat list2) list2)
(declare-fun splitAt (Nat list) pair)
(declare-fun splitAt2 (Nat list2) pair3)
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
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (times y z)) (times (times x y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (times x y) (times y x))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (plus y z)) (plus (times x y) (times x z)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times (plus x y) z) (plus (times x z) (times y z)))))
(assert (forall ((x Nat)) (= (times x (succ zero)) x)))
(assert (forall ((x Nat)) (= (times (succ zero) x) x)))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((x Nat)) (= (times x zero) zero)))
(assert (forall ((x Nat)) (= (times zero x) zero)))
(assert (isPermutation nil2 nil2))
(assert (= (stoogesort2 nil) nil))
(assert (= (length nil) zero))
(assert (= (length2 nil2) zero))
(assert (forall ((y list2)) (= (take zero y) nil2)))
(assert (forall ((z Nat)) (= (take (succ z) nil2) nil2)))
(assert
  (forall ((z Nat) (z2 sk) (xs list2))
    (= (take (succ z) (cons2 z2 xs)) (cons2 z2 (take z xs)))))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (times zero y) zero)))
(assert
  (forall ((y Nat) (z Nat))
    (= (times (succ z) y) (plus y (times z y)))))
(assert (forall ((y Nat)) (= (minus zero y) zero)))
(assert (forall ((z Nat)) (= (minus (succ z) zero) zero)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (minus (succ z) (succ y2)) (minus z y2))))
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
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
  (forall ((y Nat) (l list))
    (= (length (cons y l)) (plus (succ zero) (length l)))))
(assert
  (forall ((y sk) (l list2))
    (= (length2 (cons2 y l)) (plus (succ zero) (length2 l)))))
(assert
  (forall ((x Nat) (y Nat)) (=> (lt x y) (= (idiv x y) zero))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (not (lt x y)) (= (idiv x y) (succ (idiv (minus x y) y))))))
(assert (forall ((x sk)) (not (elem x nil2))))
(assert
  (forall ((x sk) (z sk) (xs list2))
    (= (elem x (cons2 z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((y list2)) (= (drop zero y) y)))
(assert (forall ((z Nat)) (= (drop (succ z) nil2) nil2)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list2))
    (= (drop (succ z) (cons2 z2 xs1)) (drop z xs1))))
(assert
  (forall ((x Nat) (y list2))
    (= (splitAt2 x y) (pair22 (take x y) (drop x y)))))
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
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=>
      (=
        (splitAt
          (idiv (succ (times (succ (succ zero)) (length x)))
            (succ (succ (succ zero))))
          x)
        (pair2 ys1 zs))
      (= (stooge2sort2 x) (++ (stoogesort2 ys1) zs)))))
(assert
  (forall ((y Nat)) (= (stoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat))
    (= (stoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Nat) (y2 Nat) (x3 Nat) (x4 list))
    (= (stoogesort2 (cons y (cons y2 (cons x3 x4))))
      (stooge2sort2
        (stooge2sort1 (stooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=>
      (= (splitAt (idiv (length x) (succ (succ (succ zero)))) x)
        (pair2 ys1 zs))
      (= (stooge2sort1 x) (++ ys1 (stoogesort2 zs))))))
(assert (forall ((x4 sk)) (= (apply12 lam2 x4) (lam x4))))
(assert
  (forall ((x4 sk) (x5 sk)) (= (apply14 (lam x4) x5) (= x4 x5))))
