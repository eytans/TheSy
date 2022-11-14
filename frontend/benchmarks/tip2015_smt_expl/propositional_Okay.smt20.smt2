(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 Int) (proj2-pair2 Bool))))
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype
  list5 ((nil5) (cons5 (head5 Bool) (tail5 list5))))
(declare-datatype list4 ((nil4) (cons4 (head4 Int) (tail4 list4))))
(declare-datatype list3 ((nil3) (cons3 (head3 sk) (tail3 list3))))
(declare-datatype list ((nil) (cons (head pair3) (tail list))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 list) (tail2 list2))))
(declare-datatype
  Form
  ((|:&:| (|proj1-:&:| Form) (|proj2-:&:| Form))
   (Not (proj1-Not Form)) (Var (proj1-Var Int))))
(declare-fun or2 (list5) Bool)
(declare-fun okay (list) list4)
(declare-fun models7 (Int list) list)
(declare-fun models6 (Int list) list5)
(declare-fun models5 (Int list) list)
(declare-fun models4 (Int list) list5)
(declare-fun elem (sk list3) Bool)
(declare-fun elem2 (Int list4) Bool)
(declare-fun okay2 (list) Bool)
(declare-fun formula (list2) Bool)
(declare-fun ++ (list2 list2) list2)
(declare-fun ++2 (list3 list3) list3)
(declare-fun models3 (Form list) list2)
(declare-fun models2 (Form list2) list2)
(declare-fun models (list2 Form list2) list2)
(assert (not (or2 nil5)))
(assert (= (okay nil) nil4))
(assert (okay2 nil))
(assert (formula nil2))
(assert
  (forall ((y Bool) (xs list5))
    (= (or2 (cons5 y xs)) (or y (or2 xs)))))
(assert
  (forall ((xs list) (z Int) (y2 Bool))
    (= (okay (cons (pair22 z y2) xs)) (cons4 z (okay xs)))))
(assert (forall ((x Int)) (= (models7 x nil) nil)))
(assert
  (forall ((x Int) (z pair3) (xs list))
    (=> (= x (proj1-pair2 z))
      (= (models7 x (cons z xs)) (models7 x xs)))))
(assert
  (forall ((x Int) (z pair3) (xs list))
    (=> (distinct x (proj1-pair2 z))
      (= (models7 x (cons z xs)) (cons z (models7 x xs))))))
(assert (forall ((x Int)) (= (models6 x nil) nil5)))
(assert
  (forall ((x Int) (x2 list) (y2 Int))
    (= (models6 x (cons (pair22 y2 false) x2))
      (cons5 (= x y2) (models6 x x2)))))
(assert
  (forall ((x Int) (x2 list) (y2 Int))
    (= (models6 x (cons (pair22 y2 true) x2)) (models6 x x2))))
(assert (forall ((x Int)) (= (models5 x nil) nil)))
(assert
  (forall ((x Int) (z pair3) (xs list))
    (=> (= x (proj1-pair2 z))
      (= (models5 x (cons z xs)) (models5 x xs)))))
(assert
  (forall ((x Int) (z pair3) (xs list))
    (=> (distinct x (proj1-pair2 z))
      (= (models5 x (cons z xs)) (cons z (models5 x xs))))))
(assert (forall ((x Int)) (= (models4 x nil) nil5)))
(assert
  (forall ((x Int) (x2 list) (y2 Int))
    (= (models4 x (cons (pair22 y2 false) x2)) (models4 x x2))))
(assert
  (forall ((x Int) (x2 list) (y2 Int))
    (= (models4 x (cons (pair22 y2 true) x2))
      (cons5 (= x y2) (models4 x x2)))))
(assert
  (forall ((m list) (z Int) (c2 Bool))
    (= (okay2 (cons (pair22 z c2) m))
      (and (not (elem2 z (okay m))) (okay2 m)))))
(assert
  (forall ((y list) (xs list2))
    (= (formula (cons2 y xs)) (and (okay2 y) (formula xs)))))
(assert
  (forall ((y list) (p Form) (q Form))
    (= (models3 (|:&:| p q) y) (models2 q (models3 p y)))))
(assert
  (forall ((y list) (r Form) (q2 Form))
    (= (models3 (Not (|:&:| r q2)) y)
      (++ (models3 (Not r) y) (models3 (|:&:| r (Not q2)) y)))))
(assert
  (forall ((y list) (p2 Form))
    (= (models3 (Not (Not p2)) y) (models3 p2 y))))
(assert
  (forall ((y list) (x2 Int))
    (=> (or2 (models4 x2 y)) (= (models3 (Not (Var x2)) y) nil2))))
(assert
  (forall ((y list) (x2 Int))
    (=> (not (or2 (models4 x2 y)))
      (= (models3 (Not (Var x2)) y)
        (cons2 (cons (pair22 x2 false) (models5 x2 y)) nil2)))))
(assert
  (forall ((y list) (x3 Int))
    (=> (or2 (models6 x3 y)) (= (models3 (Var x3) y) nil2))))
(assert
  (forall ((y list) (x3 Int))
    (=> (not (or2 (models6 x3 y)))
      (= (models3 (Var x3) y)
        (cons2 (cons (pair22 x3 true) (models7 x3 y)) nil2)))))
(assert (forall ((q Form)) (= (models2 q nil2) nil2)))
(assert
  (forall ((q Form) (y list) (z list2))
    (= (models2 q (cons2 y z)) (models z q (models3 q y)))))
(assert
  (forall ((x list2) (q Form)) (= (models x q nil2) (models2 q x))))
(assert
  (forall ((x list2) (q Form) (z list) (x2 list2))
    (= (models x q (cons2 z x2)) (cons2 z (models x q x2)))))
(assert (forall ((x sk)) (not (elem x nil3))))
(assert (forall ((x Int)) (not (elem2 x nil4))))
(assert
  (forall ((x sk) (z sk) (xs list3))
    (= (elem x (cons3 z xs)) (or (= z x) (elem x xs)))))
(assert
  (forall ((x Int) (z Int) (xs list4))
    (= (elem2 x (cons4 z xs)) (or (= z x) (elem2 x xs)))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert (forall ((y list3)) (= (++2 nil3 y) y)))
(assert
  (forall ((y list2) (z list) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
(assert
  (forall ((y list3) (z sk) (xs list3))
    (= (++2 (cons3 z xs) y) (cons3 z (++2 xs y)))))
