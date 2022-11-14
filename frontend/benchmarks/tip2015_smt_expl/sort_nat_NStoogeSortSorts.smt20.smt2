(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  pair4 ((pair23 (proj1-pair3 sk) (proj2-pair3 sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 list2) (proj2-pair2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-fun take (Nat list2) list2)
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun third (Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun ordered (list) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun length (list) Nat)
(declare-fun length2 (list2) Nat)
(declare-fun drop (Nat list2) list2)
(declare-fun splitAt (Nat list) pair)
(declare-fun splitAt2 (Nat list2) pair3)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun reverse (list) list)
(declare-fun reverse2 (list2) list2)
(declare-fun nstooge1sort2 (list) list)
(declare-fun nstoogesort (list) list)
(declare-fun nstooge1sort1 (list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (third zero) zero))
(assert (ordered nil))
(assert (= (nstoogesort nil) nil))
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
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y Nat)) (ordered (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (ordered (cons y (cons y2 xs)))
      (and (leq y y2) (ordered (cons y2 xs))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (not (leq x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (leq x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert
  (forall ((x list) (ys1 list) (zs1 list))
    (=> (= (splitAt (third (length x)) (reverse x)) (pair2 ys1 zs1))
      (= (nstooge1sort2 x) (++ (nstoogesort zs1) (reverse ys1))))))
(assert
  (forall ((y Nat)) (= (nstoogesort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat))
    (= (nstoogesort (cons y (cons y2 nil))) (sort2 y y2))))
(assert
  (forall ((y Nat) (y2 Nat) (x3 Nat) (x4 list))
    (= (nstoogesort (cons y (cons y2 (cons x3 x4))))
      (nstooge1sort2
        (nstooge1sort1 (nstooge1sort2 (cons y (cons y2 (cons x3 x4)))))))))
(assert
  (forall ((x list) (ys1 list) (zs list))
    (=> (= (splitAt (third (length x)) x) (pair2 ys1 zs))
      (= (nstooge1sort1 x) (++ ys1 (nstoogesort zs))))))
(assert (forall ((y list2)) (= (take zero y) nil2)))
(assert (forall ((z Nat)) (= (take (succ z) nil2) nil2)))
(assert
  (forall ((z Nat) (z2 sk) (xs list2))
    (= (take (succ z) (cons2 z2 xs)) (cons2 z2 (take z xs)))))
(assert (= (length nil) zero))
(assert (= (length2 nil2) zero))
(assert
  (forall ((y Nat) (l list))
    (= (length (cons y l)) (plus (succ zero) (length l)))))
(assert
  (forall ((y sk) (l list2))
    (= (length2 (cons2 y l)) (plus (succ zero) (length2 l)))))
(assert (forall ((y list2)) (= (drop zero y) y)))
(assert (forall ((z Nat)) (= (drop (succ z) nil2) nil2)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list2))
    (= (drop (succ z) (cons2 z2 xs1)) (drop z xs1))))
(assert
  (forall ((x Nat) (y list2))
    (= (splitAt2 x y) (pair22 (take x y) (drop x y)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert (= (reverse nil) nil))
(assert (= (reverse2 nil2) nil2))
(assert
  (forall ((y Nat) (xs list))
    (= (reverse (cons y xs)) (++ (reverse xs) (cons y nil)))))
(assert
  (forall ((y sk) (xs list2))
    (= (reverse2 (cons2 y xs)) (++2 (reverse2 xs) (cons2 y nil2)))))
