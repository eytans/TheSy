(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil) (cons (head sk) (tail list2))))
(declare-datatype list ((nil2) (cons2 (head2 Int) (tail2 list))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 Bool) (proj2-pair2 list))))
(declare-fun count (sk list2) Int)
(declare-fun bubble (list) pair3)
(declare-fun bubsort (list) list)
(assert (= (bubble nil2) (pair22 false nil2)))
(assert
  (forall ((y Int))
    (= (bubble (cons2 y nil2)) (pair22 false (cons2 y nil2)))))
(assert
  (forall ((y Int) (y2 Int) (xs list) (b12 Bool) (ys12 list))
    (=> (<= y y2)
      (=> (= (bubble (cons2 y2 xs)) (pair22 b12 ys12))
        (= (bubble (cons2 y (cons2 y2 xs)))
          (pair22 b12 (cons2 y ys12)))))))
(assert
  (forall ((y Int) (y2 Int) (xs list) (b1 Bool) (ys1 list))
    (=> (not (<= y y2))
      (=> (= (bubble (cons2 y xs)) (pair22 b1 ys1))
        (= (bubble (cons2 y (cons2 y2 xs)))
          (pair22 true (cons2 y2 ys1)))))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair22 false ys1)) (= (bubsort x) x))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair22 true ys1))
      (= (bubsort x) (bubsort ys1)))))
(assert (forall ((x sk)) (= (count x nil) 0)))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
