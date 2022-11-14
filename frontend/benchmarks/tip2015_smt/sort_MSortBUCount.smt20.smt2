(declare-sort fun1 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu (list) list2)
(declare-fun msortbu (list2) list2)
(declare-fun map2 (fun1 list2) list)
(declare-fun count (Int list2) Int)
(declare-const lam fun1)
(declare-fun apply1 (fun1 Int) list2)
(assert (= (pairwise nil) nil))
(assert (= (mergingbu nil) nil2))
(assert (forall ((f fun1)) (= (map2 f nil2) nil)))
(assert
  (forall ((f fun1) (y Int) (xs list2))
    (= (map2 f (cons2 y xs)) (cons (apply1 f y) (map2 f xs)))))
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
(assert (forall ((xs list2)) (= (mergingbu (cons xs nil)) xs)))
(assert
  (forall ((xs list2) (z list2) (x2 list))
    (= (mergingbu (cons xs (cons z x2)))
      (mergingbu (pairwise (cons xs (cons z x2)))))))
(assert
  (forall ((x list2)) (= (msortbu x) (mergingbu (map2 lam x)))))
(assert (forall ((x Int)) (= (count x nil2) 0)))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (= x z) (= (count x (cons2 z ys)) (+ 1 (count x ys))))))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (distinct x z) (= (count x (cons2 z ys)) (count x ys)))))
(assert (forall ((y Int)) (= (apply1 lam y) (cons2 y nil2))))
(assert
  (not
    (forall ((x Int) (xs list2))
      (= (count x (msortbu xs)) (count x xs)))))
(check-sat)
