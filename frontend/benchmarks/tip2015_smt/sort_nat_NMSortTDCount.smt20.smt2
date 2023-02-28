(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun take (Nat list) list)
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun nmsorttd-half1 (Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun lmerge (list list) list)
(declare-fun length (list) Nat)
(declare-fun drop (Nat list) list)
(declare-fun nmsorttd (list) list)
(declare-fun count (Nat list) Nat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (nmsorttd-half1 zero) zero))
(assert (= (nmsorttd nil) nil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (minus zero y) zero)))
(assert (forall ((z Nat)) (= (minus (succ z) zero) zero)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (minus (succ z) (succ y2)) (minus z y2))))
(assert
  (forall ((x Nat))
    (=> (= x (succ zero)) (= (nmsorttd-half1 x) zero))))
(assert
  (forall ((y Nat))
    (=> (distinct y zero)
      (= (nmsorttd-half1 (succ y))
        (plus (succ zero)
          (nmsorttd-half1 (minus (succ y) (succ (succ zero)))))))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y list)) (= (lmerge nil y) y)))
(assert
  (forall ((z Nat) (x2 list))
    (= (lmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x2 list) (x3 Nat) (x4 list))
    (=> (not (leq z x3))
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons x3 (lmerge (cons z x2) x4))))))
(assert
  (forall ((z Nat) (x2 list) (x3 Nat) (x4 list))
    (=> (leq z x3)
      (= (lmerge (cons z x2) (cons x3 x4))
        (cons z (lmerge x2 (cons x3 x4)))))))
(assert
  (forall ((y Nat)) (= (nmsorttd (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list) (k Nat))
    (=> (= k (nmsorttd-half1 (length (cons y (cons x2 x3)))))
      (= (nmsorttd (cons y (cons x2 x3)))
        (lmerge (nmsorttd (take k (cons y (cons x2 x3))))
          (nmsorttd (drop k (cons y (cons x2 x3)))))))))
(assert (forall ((y list)) (= (take zero y) nil)))
(assert (forall ((z Nat)) (= (take (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 Nat) (xs list))
    (= (take (succ z) (cons z2 xs)) (cons z2 (take z xs)))))
(assert (= (length nil) zero))
(assert
  (forall ((y Nat) (l list))
    (= (length (cons y l)) (plus (succ zero) (length l)))))
(assert (forall ((y list)) (= (drop zero y) y)))
(assert (forall ((z Nat)) (= (drop (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 Nat) (xs1 list))
    (= (drop (succ z) (cons z2 xs1)) (drop z xs1))))
(assert (forall ((x Nat)) (= (count x nil) zero)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= x z)
      (= (count x (cons z ys)) (plus (succ zero) (count x ys))))))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (nmsorttd xs)) (count x xs)))))
(check-sat)