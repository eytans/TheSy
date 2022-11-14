(declare-sort fun1 0)
(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Expr
  ((Var (proj1-Var Int)) (Lam (proj1-Lam Int) (proj2-Lam Expr))
   (App (proj1-App Expr) (proj2-App Expr))))
(declare-fun new-maximum (Int list) Int)
(declare-fun new (list) Int)
(declare-fun free (Expr) list)
(declare-fun subst (Int Expr Expr) Expr)
(declare-fun filter (fun1 list) list)
(declare-fun elem (Int list) Bool)
(declare-fun ++ (list list) list)
(declare-fun lam (Int) fun1)
(declare-fun apply1 (fun1 Int) Bool)
(assert (forall ((x Int)) (= (new-maximum x nil) x)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (not (<= x z))
      (= (new-maximum x (cons z ys)) (new-maximum x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (<= x z) (= (new-maximum x (cons z ys)) (new-maximum z ys)))))
(assert (forall ((x list)) (= (new x) (+ (new-maximum 0 x) 1))))
(assert (forall ((p fun1)) (= (filter p nil) nil)))
(assert
  (forall ((p fun1) (y Int) (xs list))
    (=> (apply1 p y)
      (= (filter p (cons y xs)) (cons y (filter p xs))))))
(assert
  (forall ((p fun1) (y Int) (xs list))
    (=> (not (apply1 p y)) (= (filter p (cons y xs)) (filter p xs)))))
(assert (forall ((x Int)) (not (elem x nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Int) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y Int)) (= (free (Var y)) (cons y nil))))
(assert
  (forall ((z Int) (b Expr))
    (= (free (Lam z b)) (filter (lam z) (free b)))))
(assert
  (forall ((a2 Expr) (b2 Expr))
    (= (free (App a2 b2)) (++ (free a2) (free b2)))))
(assert
  (forall ((x Int) (y Expr) (y2 Int))
    (=> (= x y2) (= (subst x y (Var y2)) y))))
(assert
  (forall ((x Int) (y Expr) (y2 Int))
    (=> (distinct x y2) (= (subst x y (Var y2)) (Var y2)))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++ (free y) (free a))))
      (=> (= x y3) (= (subst x y (Lam y3 a)) (Lam y3 a))))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++ (free y) (free a))))
      (=> (distinct x y3)
        (=> (elem y3 (free y))
          (= (subst x y (Lam y3 a))
            (subst x y (Lam z2 (subst y3 (Var z2) a)))))))))
(assert
  (forall ((x Int) (y Expr) (y3 Int) (a Expr) (z2 Int))
    (=> (= z2 (new (++ (free y) (free a))))
      (=> (distinct x y3)
        (=> (not (elem y3 (free y)))
          (= (subst x y (Lam y3 a)) (Lam y3 (subst x y a))))))))
(assert
  (forall ((x Int) (y Expr) (a2 Expr) (b2 Expr))
    (= (subst x y (App a2 b2)) (App (subst x y a2) (subst x y b2)))))
(assert
  (forall ((z Int) (x2 Int))
    (= (apply1 (lam z) x2) (distinct z x2))))
(assert
  (not
    (forall ((x Int) (e Expr) (a Expr) (y Int))
      (=> (not (elem x (free a)))
        (= (elem y (free a)) (elem y (free (subst x e a))))))))
(check-sat)
