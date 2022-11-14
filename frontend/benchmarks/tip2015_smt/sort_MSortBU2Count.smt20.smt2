(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun risers (list2) list)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu2 (list) list2)
(declare-fun msortbu2 (list2) list2)
(declare-fun count (Int list2) Int)
(assert (= (risers nil2) nil))
(assert (= (pairwise nil) nil))
(assert (= (mergingbu2 nil) nil2))
(assert
  (forall ((y Int))
    (= (risers (cons2 y nil2)) (cons (cons2 y nil2) nil))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (=> (not (<= y y2))
      (= (risers (cons2 y (cons2 y2 xs)))
        (cons (cons2 y nil2) (risers (cons2 y2 xs)))))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (=> (<= y y2)
      (=> (= (risers (cons2 y2 xs)) nil)
        (= (risers (cons2 y (cons2 y2 xs))) nil)))))
(assert
  (forall ((y Int) (y2 Int) (xs list2) (ys list2) (yss list))
    (=> (<= y y2)
      (=> (= (risers (cons2 y2 xs)) (cons ys yss))
        (= (risers (cons2 y (cons2 y2 xs))) (cons (cons2 y ys) yss))))))
(assert (forall ((y list2)) (= (lmerge nil2 y) y)))
(assert
  (forall ((z Int) (x2 list2))
    (= (lmerge (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (not (<= z x3))
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 x3 (lmerge (cons2 z x2) x4))))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (<= z x3)
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
  (forall ((x list2)) (= (msortbu2 x) (mergingbu2 (risers x)))))
(assert (forall ((x Int)) (= (count x nil2) 0)))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (distinct x z) (= (count x (cons2 z ys)) (count x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (= x z) (= (count x (cons2 z ys)) (+ 1 (count x ys))))))
(assert
  (not
    (forall ((x Int) (xs list2))
      (= (count x (msortbu2 xs)) (count x xs)))))
(check-sat)
