(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun sort2 (Int Int) list2)
(declare-fun insert2 (Int list2) list2)
(declare-fun isort (list2) list2)
(declare-fun evens (list) list)
(declare-fun evens2 (list2) list2)
(declare-fun odds (list) list)
(declare-fun odds2 (list2) list2)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun pairs (list2 list2) list2)
(declare-fun stitch (list2 list2) list2)
(declare-fun bmerge (list2 list2) list2)
(declare-fun bsort (list2) list2)
(assert (= (isort nil2) nil2))
(assert (= (bsort nil2) nil2))
(assert
  (forall ((x Int) (y Int))
    (=> (not (<= x y)) (= (sort2 x y) (cons2 y (cons2 x nil2))))))
(assert
  (forall ((x Int) (y Int))
    (=> (<= x y) (= (sort2 x y) (cons2 x (cons2 y nil2))))))
(assert (forall ((x Int)) (= (insert2 x nil2) (cons2 x nil2))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (not (<= x z))
      (= (insert2 x (cons2 z xs)) (cons2 z (insert2 x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (=> (<= x z) (= (insert2 x (cons2 z xs)) (cons2 x (cons2 z xs))))))
(assert
  (forall ((y Int) (xs list2))
    (= (isort (cons2 y xs)) (insert2 y (isort xs)))))
(assert (forall ((y list2)) (= (pairs nil2 y) y)))
(assert
  (forall ((z Int) (x2 list2))
    (= (pairs (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall ((z Int) (x2 list2) (x3 Int) (x4 list2))
    (= (pairs (cons2 z x2) (cons2 x3 x4))
      (++2 (sort2 z x3) (pairs x2 x4)))))
(assert (forall ((y list2)) (= (stitch nil2 y) y)))
(assert
  (forall ((y list2) (z Int) (xs list2))
    (= (stitch (cons2 z xs) y) (cons2 z (pairs xs y)))))
(assert (forall ((y list2)) (= (bmerge nil2 y) nil2)))
(assert
  (forall ((z Int) (x2 list2))
    (= (bmerge (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall
    ((z Int) (x3 Int) (x4 list2) (fail list2) (x7 Int) (x8 list2))
    (=>
      (= fail
        (stitch
          (bmerge (evens2 (cons2 z (cons2 x7 x8))) (evens2 (cons2 x3 x4)))
          (bmerge (odds2 (cons2 z (cons2 x7 x8))) (odds2 (cons2 x3 x4)))))
      (= (bmerge (cons2 z (cons2 x7 x8)) (cons2 x3 x4)) fail))))
(assert
  (forall ((z Int) (x3 Int) (fail list2))
    (=>
      (= fail
        (stitch (bmerge (evens2 (cons2 z nil2)) (evens2 (cons2 x3 nil2)))
          (bmerge (odds2 (cons2 z nil2)) (odds2 (cons2 x3 nil2)))))
      (= (bmerge (cons2 z nil2) (cons2 x3 nil2)) (sort2 z x3)))))
(assert
  (forall ((z Int) (x3 Int) (fail list2) (x5 Int) (x6 list2))
    (=>
      (= fail
        (stitch
          (bmerge (evens2 (cons2 z nil2)) (evens2 (cons2 x3 (cons2 x5 x6))))
          (bmerge (odds2 (cons2 z nil2)) (odds2 (cons2 x3 (cons2 x5 x6))))))
      (= (bmerge (cons2 z nil2) (cons2 x3 (cons2 x5 x6))) fail))))
(assert
  (forall ((y Int)) (= (bsort (cons2 y nil2)) (cons2 y nil2))))
(assert
  (forall ((y Int) (x2 Int) (x3 list2))
    (= (bsort (cons2 y (cons2 x2 x3)))
      (bmerge (bsort (evens2 (cons2 y (cons2 x2 x3))))
        (bsort (odds2 (cons2 y (cons2 x2 x3))))))))
(assert (= (evens nil) nil))
(assert (= (evens2 nil2) nil2))
(assert
  (forall ((y sk) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert
  (forall ((y Int) (xs list2))
    (= (evens2 (cons2 y xs)) (cons2 y (odds2 xs)))))
(assert (= (odds nil) nil))
(assert (= (odds2 nil2) nil2))
(assert
  (forall ((y sk) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert
  (forall ((y Int) (xs list2)) (= (odds2 (cons2 y xs)) (evens2 xs))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y list2) (z Int) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
