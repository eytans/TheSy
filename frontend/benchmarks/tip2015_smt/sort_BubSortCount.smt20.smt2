(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  pair ((pair2 (proj1-pair Bool) (proj2-pair list))))
(declare-fun count (Int list) Int)
(declare-fun bubble (list) pair)
(declare-fun bubsort (list) list)
(assert (= (bubble nil) (pair2 false nil)))
(assert
  (forall ((y Int))
    (= (bubble (cons y nil)) (pair2 false (cons y nil)))))
(assert
  (forall ((y Int) (y2 Int) (xs list) (b12 Bool) (ys12 list))
    (=> (<= y y2)
      (=> (= (bubble (cons y2 xs)) (pair2 b12 ys12))
        (= (bubble (cons y (cons y2 xs))) (pair2 b12 (cons y ys12)))))))
(assert
  (forall ((y Int) (y2 Int) (xs list) (b1 Bool) (ys1 list))
    (=> (not (<= y y2))
      (=> (= (bubble (cons y xs)) (pair2 b1 ys1))
        (= (bubble (cons y (cons y2 xs))) (pair2 true (cons y2 ys1)))))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair2 false ys1)) (= (bubsort x) x))))
(assert
  (forall ((x list) (ys1 list))
    (=> (= (bubble x) (pair2 true ys1))
      (= (bubsort x) (bubsort ys1)))))
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (bubsort xs)) (count x xs)))))
(check-sat)
