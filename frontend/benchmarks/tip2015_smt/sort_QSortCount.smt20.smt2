(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-fun qsort (list) list)
(declare-fun filter (fun1 list) list)
(declare-fun count (Int list) Int)
(declare-fun ++ (list list) list)
(declare-fun lam (Int) fun1)
(declare-fun lam2 (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(assert (= (qsort nil) nil))
(assert (forall ((p fun1)) (= (filter p nil) nil)))
(assert
  (forall ((p fun1) (y Int) (xs list))
    (=> (apply1 p y)
      (= (filter p (cons y xs)) (cons y (filter p xs))))))
(assert
  (forall ((p fun1) (y Int) (xs list))
    (=> (not (apply1 p y)) (= (filter p (cons y xs)) (filter p xs)))))
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y Int) (xs list))
    (= (qsort (cons y xs))
      (++ (qsort (filter (lam y) xs))
        (++ (cons y nil) (qsort (filter (lam2 y) xs)))))))
(assert (forall ((y Int) (z Int)) (= (apply1 (lam y) z) (<= z y))))
(assert
  (forall ((y Int) (x2 Int)) (= (apply1 (lam2 y) x2) (> x2 y))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (qsort xs)) (count x xs)))))
(check-sat)