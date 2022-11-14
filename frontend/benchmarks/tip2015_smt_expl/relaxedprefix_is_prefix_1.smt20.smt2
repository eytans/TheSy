(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype It ((A) (B) (C)))
(declare-datatype list ((nil) (cons (head It) (tail list))))
(declare-fun isPrefix (list list) Bool)
(declare-fun isRelaxedPrefix (list list) Bool)
(declare-fun ++ (list2 list2) list2)
(assert (forall ((y list)) (isPrefix nil y)))
(assert
  (forall ((z It) (x2 list)) (not (isPrefix (cons z x2) nil))))
(assert
  (forall ((z It) (x2 list) (x3 It) (x4 list))
    (= (isPrefix (cons z x2) (cons x3 x4))
      (and (= z x3) (isPrefix x2 x4)))))
(assert (forall ((y list)) (isRelaxedPrefix nil y)))
(assert
  (forall ((y list) (z It)) (isRelaxedPrefix (cons z nil) y)))
(assert
  (forall ((z It) (x3 It) (x4 list))
    (not (isRelaxedPrefix (cons z (cons x3 x4)) nil))))
(assert
  (forall ((z It) (x3 It) (x4 list) (x5 It) (x6 list))
    (=> (distinct z x5)
      (= (isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6))
        (isPrefix (cons x3 x4) (cons x5 x6))))))
(assert
  (forall ((z It) (x3 It) (x4 list) (x5 It) (x6 list))
    (=> (= z x5)
      (= (isRelaxedPrefix (cons z (cons x3 x4)) (cons x5 x6))
        (isRelaxedPrefix (cons x3 x4) x6)))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
