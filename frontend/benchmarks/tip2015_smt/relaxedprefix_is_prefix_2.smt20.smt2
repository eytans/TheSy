(declare-datatype It ((A) (B) (C)))
(declare-datatype list ((nil) (cons (head It) (tail list))))
(declare-fun isPrefix (list list) Bool)
(declare-fun isRelaxedPrefix (list list) Bool)
(declare-fun ++ (list list) list)
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
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z It) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((x It) (xs list) (ys list) (zs list))
      (isRelaxedPrefix (++ xs (++ (cons x nil) ys))
        (++ xs (++ ys zs))))))
(check-sat)
