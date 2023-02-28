(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun return (sk) list)
(declare-fun ++ (list list) list)
(declare-fun >>= (list fun12) list)
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list)
(assert (forall ((x sk)) (= (return x) (cons x nil))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y fun12)) (= (>>= nil y) nil)))
(assert
  (forall ((y fun12) (z sk) (xs list))
    (= (>>= (cons z xs) y) (++ (apply12 y z) (>>= xs y)))))
(assert (forall ((x sk)) (= (apply12 lam x) (return x))))
(assert (not (forall ((xs list)) (= (>>= xs lam) xs))))
(check-sat)