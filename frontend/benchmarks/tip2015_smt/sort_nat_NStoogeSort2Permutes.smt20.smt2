(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun third (Nat) Nat)
(declare-fun twoThirds (Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun length (list) Nat)
(declare-fun splitAt (Nat list) pair)
(declare-fun isPermutation (list list) Bool)
(declare-fun ++ (list list) list)
(declare-fun nstooge2sort2 (list) list)
(declare-fun nstoogesort2 (list) list)
(declare-fun nstooge2sort1 (list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (third zero) zero))
(assert (= (twoThirds zero) zero))
(assert (= (nstoogesort2 nil) nil))
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
    (=> (distinct x (succ (succ zero)))
      (=> (= x (succ zero)) (= (third x) zero)))))
(assert
  (forall ((x Nat))
    (=> (= x (succ (succ zero))) (= (third x) zero))))
(assert
  (forall ((y Nat))
    (=> (distinct y (succ zero))
      (=> (distinct y zero)
        (= (third (succ y))
          (plus (succ zero)
            (third (minus (succ y) (succ (succ (succ zero)))))))))))
(assert
  (forall ((x Nat))
    (=> (distinct x (succ (succ zero)))
      (=> (= x (succ zero)) (= (twoThirds x) (succ zero))))))
(assert
  (forall ((x Nat))
    (=> (= x (succ (succ zero))) (= (twoThirds x) (succ zero)))))
(assert
  (forall ((y Nat))
    (=> (distinct y (succ zero))
      (=> (distinct y zero)
        (= (twoThirds (succ y))
          (plus (succ (succ zero))
            (twoThirds (minus (succ y) (succ (succ (succ zero)))))))))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (not (leq x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (leq x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (twoThirds (length x)) x) (pair2 ys1 zs))
      (= (nstooge2sort2 x) (++ (nstoogesort2 ys1) zs)))))
(assert
  (forall ((y Nat)) (= (nstoogesort2 (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat))
    (= (nstoogesort2 (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Nat) (y2 Nat) (x3 Nat) (x4 list))
    (= (nstoogesort2 (cons y (cons y2 (cons x3 x4))))
      (nstooge2sort2
        (nstooge2sort1 (nstooge2sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (third (length x)) x) (pair2 ys1 zs))
      (= (nstooge2sort1 x) (++ ys1 (nstoogesort2 zs))))))
(assert (= (length nil) zero))
(assert
  (forall ((y Nat) (l list))
    (= (length (cons y l)) (plus (succ zero) (length l)))))
(assert (isPermutation nil nil))
(assert
  (forall ((z Nat) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not (forall ((xs list)) (isPermutation (nstoogesort2 xs) xs))))
(check-sat)
