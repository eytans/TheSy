(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun ssort-minimum1 (Nat list) Nat)
(declare-fun ssort (list) list)
(declare-fun deleteBy (fun1 Nat list) list)
(declare-fun count (Nat list) Nat)
(declare-fun lam (Nat) fun12)
(declare-const lam2 fun1)
(declare-fun apply1 (fun1 Nat) fun12)
(declare-fun apply12 (fun12 Nat) Bool)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (ssort nil) nil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((x Nat)) (= (ssort-minimum1 x nil) x)))
(assert
  (forall ((x Nat) (y1 Nat) (ys1 list))
    (=> (leq y1 x)
      (= (ssort-minimum1 x (cons y1 ys1)) (ssort-minimum1 y1 ys1)))))
(assert
  (forall ((x Nat) (y1 Nat) (ys1 list))
    (=> (not (leq y1 x))
      (= (ssort-minimum1 x (cons y1 ys1)) (ssort-minimum1 x ys1)))))
(assert (forall ((x fun1) (y Nat)) (= (deleteBy x y nil) nil)))
(assert
  (forall ((x fun1) (y Nat) (y2 Nat) (ys list))
    (=> (apply12 (apply1 x y) y2) (= (deleteBy x y (cons y2 ys)) ys))))
(assert
  (forall ((x fun1) (y Nat) (y2 Nat) (ys list))
    (=> (not (apply12 (apply1 x y) y2))
      (= (deleteBy x y (cons y2 ys)) (cons y2 (deleteBy x y ys))))))
(assert
  (forall ((y Nat) (ys list) (m Nat))
    (=> (= m (ssort-minimum1 y ys))
      (= (ssort (cons y ys))
        (cons m (ssort (deleteBy lam2 m (cons y ys))))))))
(assert (forall ((x Nat)) (= (count x nil) zero)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= x z)
      (= (count x (cons z ys)) (plus (succ zero) (count x ys))))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert (forall ((z Nat)) (= (apply1 lam2 z) (lam z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (apply12 (lam z) x2) (= z x2))))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (ssort xs)) (count x xs)))))
(check-sat)
