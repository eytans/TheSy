(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list2 ((nil2) (cons2 (head2 Nat) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu2 (list) list2)
(declare-fun risers (list2) list)
(declare-fun msortbu2 (list2) list2)
(declare-fun count (Nat list2) Nat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (pairwise nil) nil))
(assert (= (mergingbu2 nil) nil2))
(assert (= (risers nil2) nil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y list2)) (= (lmerge nil2 y) y)))
(assert
  (forall ((z Nat) (x2 list2))
    (= (lmerge (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall ((z Nat) (x2 list2) (x3 Nat) (x4 list2))
    (=> (not (leq z x3))
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 x3 (lmerge (cons2 z x2) x4))))))
(assert
  (forall ((z Nat) (x2 list2) (x3 Nat) (x4 list2))
    (=> (leq z x3)
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 z (lmerge x2 (cons2 x3 x4)))))))
(assert
  (forall ((xs list2)) (= (pairwise (cons xs nil)) (cons xs nil))))
(assert
  (forall ((xs list2) (ys list2) (xss list))
    (= (pairwise (cons xs (cons ys xss)))
      (cons (lmerge xs ys) (pairwise xss)))))
(assert (forall ((xs list2)) (= (mergingbu2 (cons xs nil)) xs)))
(assert
  (forall ((xs list2) (z list2) (x2 list))
    (= (mergingbu2 (cons xs (cons z x2)))
      (mergingbu2 (pairwise (cons xs (cons z x2)))))))
(assert
  (forall ((y Nat))
    (= (risers (cons2 y nil2)) (cons (cons2 y nil2) nil))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list2))
    (=> (not (leq y y2))
      (= (risers (cons2 y (cons2 y2 xs)))
        (cons (cons2 y nil2) (risers (cons2 y2 xs)))))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list2))
    (=> (leq y y2)
      (=> (= (risers (cons2 y2 xs)) nil)
        (= (risers (cons2 y (cons2 y2 xs))) nil)))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list2) (ys list2) (yss list))
    (=> (leq y y2)
      (=> (= (risers (cons2 y2 xs)) (cons ys yss))
        (= (risers (cons2 y (cons2 y2 xs))) (cons (cons2 y ys) yss))))))
(assert
  (forall ((x list2)) (= (msortbu2 x) (mergingbu2 (risers x)))))
(assert (forall ((x Nat)) (= (count x nil2) zero)))
(assert
  (forall ((x Nat) (z Nat) (ys list2))
    (=> (distinct x z) (= (count x (cons2 z ys)) (count x ys)))))
(assert
  (forall ((x Nat) (z Nat) (ys list2))
    (=> (= x z)
      (= (count x (cons2 z ys)) (plus (succ zero) (count x ys))))))
(assert
  (not
    (forall ((x Nat) (xs list2))
      (= (count x (msortbu2 xs)) (count x xs)))))
(check-sat)
