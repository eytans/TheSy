(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun weird_concat (list) list2)
(declare-fun map2 (fun12 list2) list)
(declare-fun map3 (fun1 list2) list2)
(declare-fun ++ (list2 list2) list2)
(declare-fun >>= (list2 fun12) list2)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list2)
(assert (= (weird_concat nil) nil2))
(assert
  (forall ((xss list))
    (= (weird_concat (cons nil2 xss)) (weird_concat xss))))
(assert
  (forall ((xss list) (z sk) (xs list2))
    (= (weird_concat (cons (cons2 z xs) xss))
      (cons2 z (weird_concat (cons xs xss))))))
(assert (forall ((f fun1)) (= (map3 f nil2) nil2)))
(assert
  (forall ((f fun1) (y sk) (xs list2))
    (= (map3 f (cons2 y xs)) (cons2 (apply1 f y) (map3 f xs)))))
(assert (forall ((f fun12)) (= (map2 f nil2) nil)))
(assert
  (forall ((f fun12) (y sk) (xs list2))
    (= (map2 f (cons2 y xs)) (cons (apply12 f y) (map2 f xs)))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
(assert (forall ((y fun12)) (= (>>= nil2 y) nil2)))
(assert
  (forall ((y fun12) (z sk) (xs list2))
    (= (>>= (cons2 z xs) y) (++ (apply12 y z) (>>= xs y)))))
(assert
  (not
    (forall ((f fun12) (xs list2))
      (= (weird_concat (map2 f xs)) (>>= xs f)))))
(check-sat)
