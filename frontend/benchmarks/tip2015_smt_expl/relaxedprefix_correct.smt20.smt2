(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  list4 ((nil4) (cons4 (head4 Bool) (tail4 list4))))
(declare-datatype list3 ((nil3) (cons3 (head3 sk) (tail3 list3))))
(declare-datatype It ((A) (B) (C)))
(declare-datatype list2 ((nil2) (cons2 (head2 It) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun removeOne (It list) list)
(declare-fun removeOne2 (list2) list)
(declare-fun or2 (list4) Bool)
(declare-fun isPrefix (list2 list2) Bool)
(declare-fun isRelaxedPrefix (list2 list2) Bool)
(declare-fun spec (list2 list) list4)
(declare-fun spec2 (list2 list2) Bool)
(assert (= (removeOne2 nil2) nil))
(assert (not (or2 nil4)))
(assert (forall ((x It)) (= (removeOne x nil) nil)))
(assert
  (forall ((x It) (z list2) (x2 list))
    (= (removeOne x (cons z x2)) (cons (cons2 x z) (removeOne x x2)))))
(assert
  (forall ((y It) (xs list2))
    (= (removeOne2 (cons2 y xs))
      (cons xs (removeOne y (removeOne2 xs))))))
(assert
  (forall ((y Bool) (xs list4))
    (= (or2 (cons4 y xs)) (or y (or2 xs)))))
(assert (forall ((y list2)) (isPrefix nil2 y)))
(assert
  (forall ((z It) (x2 list2)) (not (isPrefix (cons2 z x2) nil2))))
(assert
  (forall ((z It) (x2 list2) (x3 It) (x4 list2))
    (= (isPrefix (cons2 z x2) (cons2 x3 x4))
      (and (= z x3) (isPrefix x2 x4)))))
(assert (forall ((y list2)) (isRelaxedPrefix nil2 y)))
(assert
  (forall ((y list2) (z It)) (isRelaxedPrefix (cons2 z nil2) y)))
(assert
  (forall ((z It) (x3 It) (x4 list2))
    (not (isRelaxedPrefix (cons2 z (cons2 x3 x4)) nil2))))
(assert
  (forall ((z It) (x3 It) (x4 list2) (x5 It) (x6 list2))
    (=> (distinct z x5)
      (= (isRelaxedPrefix (cons2 z (cons2 x3 x4)) (cons2 x5 x6))
        (isPrefix (cons2 x3 x4) (cons2 x5 x6))))))
(assert
  (forall ((z It) (x3 It) (x4 list2) (x5 It) (x6 list2))
    (=> (= z x5)
      (= (isRelaxedPrefix (cons2 z (cons2 x3 x4)) (cons2 x5 x6))
        (isRelaxedPrefix (cons2 x3 x4) x6)))))
(assert (forall ((ys list2)) (= (spec ys nil) nil4)))
(assert
  (forall ((ys list2) (y list2) (z list))
    (= (spec ys (cons y z)) (cons4 (isPrefix y ys) (spec ys z)))))
(assert
  (forall ((x list2) (y list2))
    (= (spec2 x y) (or2 (spec y (cons x (removeOne2 x)))))))
