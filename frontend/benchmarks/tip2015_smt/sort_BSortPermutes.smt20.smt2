(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun sort2 (Int Int) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun ++ (list list) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(assert (= (bsort nil) nil))
(assert
  (forall ((x Int) (y Int))
    (=> (not (<= x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Int) (y Int))
    (=> (<= x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert (forall ((y list)) (= (pairs nil y) y)))
(assert
  (forall ((z Int) (x2 list))
    (= (pairs (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Int) (x2 list) (x3 Int) (x4 list))
    (= (pairs (cons z x2) (cons x3 x4))
      (++ (sort2 z x3) (pairs x2 x4)))))
(assert (forall ((y list)) (= (stitch nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (stitch (cons z xs) y) (cons z (pairs xs y)))))
(assert (forall ((y list)) (= (bmerge nil y) nil)))
(assert
  (forall ((z Int) (x2 list))
    (= (bmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Int) (x3 Int) (x4 list) (fail list) (x7 Int) (x8 list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z (cons x7 x8))) (evens (cons x3 x4)))
          (bmerge (odds (cons z (cons x7 x8))) (odds (cons x3 x4)))))
      (= (bmerge (cons z (cons x7 x8)) (cons x3 x4)) fail))))
(assert
  (forall ((z Int) (x3 Int) (fail list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z nil)) (evens (cons x3 nil)))
          (bmerge (odds (cons z nil)) (odds (cons x3 nil)))))
      (= (bmerge (cons z nil) (cons x3 nil)) (sort2 z x3)))))
(assert
  (forall ((z Int) (x3 Int) (fail list) (x5 Int) (x6 list))
    (=>
      (= fail
        (stitch
          (bmerge (evens (cons z nil)) (evens (cons x3 (cons x5 x6))))
          (bmerge (odds (cons z nil)) (odds (cons x3 (cons x5 x6))))))
      (= (bmerge (cons z nil) (cons x3 (cons x5 x6))) fail))))
(assert (forall ((y Int)) (= (bsort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Int) (x2 Int) (x3 list))
    (= (bsort (cons y (cons x2 x3)))
      (bmerge (bsort (evens (cons y (cons x2 x3))))
        (bsort (odds (cons y (cons x2 x3))))))))
(assert (= (evens nil) nil))
(assert
  (forall ((y Int) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert (= (odds nil) nil))
(assert
  (forall ((y Int) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert (isPermutation nil nil))
(assert
  (forall ((z Int) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (not (forall ((xs list)) (isPermutation (bsort xs) xs))))
(check-sat)
