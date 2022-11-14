(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 Bool) (proj2-pair2 list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun ordered (list) Bool)
(declare-fun bubble (list) pair3)
(declare-fun bubsort (list) list)
(assert (ordered nil))
(assert (= (bubble nil) (pair22 false nil)))
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
