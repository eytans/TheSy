(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair Bool) (proj2-pair list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun count (Nat list) Nat)
(declare-fun bubble (list) pair)
(declare-fun bubsort (list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (bubble nil) (pair2 false nil)))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (forall ((y Nat))
    (= (bubble (cons y nil)) (pair2 false (cons y nil)))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (b12 Bool) (ys12 list))
    (=> (leq y y2)
      (=> (= (bubble (cons y2 xs)) (pair2 b12 ys12))
        (= (bubble (cons y (cons y2 xs))) (pair2 b12 (cons y ys12)))))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list) (b1 Bool) (ys1 list))
    (=> (not (leq y y2))
      (=> (= (bubble (cons y xs)) (pair2 b1 ys1))
        (= (bubble (cons y (cons y2 xs))) (pair2 true (cons y2 ys1)))))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair2 false ys1)) (= (bubsort x) x))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair2 true ys1))
      (= (bubsort x) (bubsort ys1)))))
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
      (= (count x (bubsort xs)) (count x xs)))))
(check-sat)
