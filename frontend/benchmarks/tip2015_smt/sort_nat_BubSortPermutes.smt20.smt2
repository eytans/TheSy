(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair Bool) (proj2-pair list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun isPermutation (list list) Bool)
(declare-fun bubble (list) pair)
(declare-fun bubsort (list) list)
(assert (= (bubble nil) (pair2 false nil)))
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
(assert (isPermutation nil nil))
(assert
  (forall ((z Nat) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (not (forall ((xs list)) (isPermutation (bubsort xs) xs))))
(check-sat)
