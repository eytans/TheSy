(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun takeWhile (fun12 list) list)
(declare-fun dropWhile (fun12 list) list)
(declare-fun ++ (list list) list)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(assert (forall ((x fun12)) (= (takeWhile x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (apply12 x z)
      (= (takeWhile x (cons z xs)) (cons z (takeWhile x xs))))))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (not (apply12 x z)) (= (takeWhile x (cons z xs)) nil))))
(assert (forall ((x fun12)) (= (dropWhile x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (apply12 x z) (= (dropWhile x (cons z xs)) (dropWhile x xs)))))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (not (apply12 x z))
      (= (dropWhile x (cons z xs)) (cons z xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((p fun12) (xs list))
      (= (++ (takeWhile p xs) (dropWhile p xs)) xs))))
(check-sat)
