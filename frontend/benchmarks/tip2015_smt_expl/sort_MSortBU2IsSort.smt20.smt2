(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list3 ((nil2) (cons2 (head2 sk) (tail2 list3))))
(declare-datatype list2 ((nil3) (cons3 (head3 Int) (tail3 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun risers (list2) list)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu2 (list) list2)
(declare-fun msortbu2 (list2) list2)
(declare-fun insert2 (Int list2) list2)
(declare-fun isort (list2) list2)
(assert (= (risers nil3) nil))
(assert (= (pairwise nil) nil))
(assert (= (mergingbu2 nil) nil3))
(assert (= (isort nil3) nil3))
(assert
  (forall ((y Int))
    (= (risers (cons3 y nil3)) (cons (cons3 y nil3) nil))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (=> (not (<= y y2))
      (= (risers (cons3 y (cons3 y2 xs)))
        (cons (cons3 y nil3) (risers (cons3 y2 xs)))))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (=> (<= y y2)
      (=> (= (risers (cons3 y2 xs)) nil)
        (= (risers (cons3 y (cons3 y2 xs))) nil)))))
(assert
  (forall ((y Int) (y2 Int) (xs list2) (ys list2) (yss list))
    (=> (<= y y2)
      (=> (= (risers (cons3 y2 xs)) (cons ys yss))
        (= (risers (cons3 y (cons3 y2 xs))) (cons (cons3 y ys) yss))))))
(assert (forall ((y list2)) (= (lmerge nil3 y) y)))
(assert
  (forall ((z Int) (x2 list2))
    (= (lmerge (cons3 z x2) nil3) (cons3 z x2))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (not (<= z x3))
      (= (lmerge (cons3 z x2) (cons3 x3 x4))
        (cons3 x3 (lmerge (cons3 z x2) x4))))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (=> (<= z x3)
      (= (lmerge (cons3 z x2) (cons3 x3 x4))
        (cons3 z (lmerge x2 (cons3 x3 x4)))))))
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
(assert (forall ((x Int)) (= (insert2 x nil3) (cons3 x nil3))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (not (<= x z))
      (= (insert2 x (cons3 z xs)) (cons3 z (insert2 x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (<= x z) (= (insert2 x (cons3 z xs)) (cons3 x (cons3 z xs))))))
(assert
  (forall ((y Int) (xs list2))
    (= (isort (cons3 y xs)) (insert2 y (isort xs)))))
