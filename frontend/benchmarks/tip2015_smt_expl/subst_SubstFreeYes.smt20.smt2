(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort fun16 0)
(declare-sort sk2 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Expr
  ((Var (proj1-Var Int)) (Lam (proj1-Lam Int) (proj2-Lam Expr))
   (App (proj1-App Expr) (proj2-App Expr))))
(declare-fun new-maximum (Int list2) Int)
(declare-fun new (list2) Int)
(declare-fun free (Expr) list2)
(declare-fun subst (Int Expr Expr) Expr)
(declare-fun filter (fun13 list) list)
(declare-fun filter2 (fun16 list2) list2)
(declare-fun elem (sk list) Bool)
(declare-fun elem2 (Int list2) Bool)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun lam (Int) fun16)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) sk2)
(declare-fun apply13 (fun13 sk) Bool)
(declare-fun apply14 (fun14 sk2) sk)
(declare-fun apply15 (fun15 sk2) sk2)
(declare-fun apply16 (fun16 Int) Bool)
(assert (forall ((x Int)) (= (new-maximum x nil2) x)))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (not (<= x z))
      (= (new-maximum x (cons2 z ys)) (new-maximum x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list2))
    (=> (<= x z) (= (new-maximum x (cons2 z ys)) (new-maximum z ys)))))
(assert (forall ((x list2)) (= (new x) (+ (new-maximum 0 x) 1))))
(assert (forall ((p fun13)) (= (filter p nil) nil)))
(assert
  (forall ((p fun13) (y sk) (xs list))
    (=> (apply13 p y)
      (= (filter p (cons y xs)) (cons y (filter p xs))))))
(assert
  (forall ((p fun13) (y sk) (xs list))
    (=> (not (apply13 p y)) (= (filter p (cons y xs)) (filter p xs)))))
(assert (forall ((p fun16)) (= (filter2 p nil2) nil2)))
(assert
  (forall ((p fun16) (y Int) (xs list2))
    (=> (apply16 p y)
      (= (filter2 p (cons2 y xs)) (cons2 y (filter2 p xs))))))
(assert
  (forall ((p fun16) (y Int) (xs list2))
    (=> (not (apply16 p y))
      (= (filter2 p (cons2 y xs)) (filter2 p xs)))))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((x Int)) (not (elem2 x nil2))))
(assert
  (forall ((x Int) (z Int) (xs list2))
    (= (elem2 x (cons2 z xs)) (or (= z x) (elem2 x xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list2) (z Int) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert (forall ((y Int)) (= (free (Var y)) (cons2 y nil2))))
(assert
  (forall ((z Int) (b Expr))
    (= (free (Lam z b)) (filter2 (lam z) (free b)))))
(assert
  (forall ((a2 Expr) (b2 Expr))
    (= (free (App a2 b2)) (++2 (free a2) (free b2)))))
(assert
  (forall ((x Int) (y Expr) (y2 Int))
    (=> (= x y2) (= (subst x y (Var y2)) y))))
(assert
  (forall ((x Int) (y Expr) (y2 Int))
    (=> (distinct x y2) (= (subst x y (Var y2)) (Var y2)))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++2 (free y) (free a))))
      (=> (= x y3) (= (subst x y (Lam y3 a)) (Lam y3 a))))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++2 (free y) (free a))))
      (=> (distinct x y3)
        (=> (elem2 y3 (free y))
          (= (subst x y (Lam y3 a))
            (subst x y (Lam z2 (subst y3 (Var z2) a)))))))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++2 (free y) (free a))))
      (=> (distinct x y3)
        (=> (not (elem2 y3 (free y)))
          (= (subst x y (Lam y3 a)) (Lam y3 (subst x y a))))))))
(assert
  (forall ((x Int) (y Expr) (a2 Expr) (b2 Expr))
    (= (subst x y (App a2 b2)) (App (subst x y a2) (subst x y b2)))))
(assert
  (forall ((z Int) (x2 Int))
    (= (apply16 (lam z) x2) (distinct z x2))))
