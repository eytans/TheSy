(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun evens (list) list)
(declare-fun odds (list) list)
(declare-fun count (Nat list) Nat)
(declare-fun ++ (list list) list)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (bsort nil) nil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (not (leq x y)) (= (sort2 x y) (cons y (cons x nil))))))
(assert
  (forall ((x Nat) (y Nat))
    (=> (leq x y) (= (sort2 x y) (cons x (cons y nil))))))
(assert (forall ((y list)) (= (pairs nil y) y)))
(assert
  (forall ((z Nat) (x2 list))
    (= (pairs (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x2 list) (x3 Nat) (x4 list))
    (= (pairs (cons z x2) (cons x3 x4))
      (++ (sort2 z x3) (pairs x2 x4)))))
(assert (forall ((y list)) (= (stitch nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (stitch (cons z xs) y) (cons z (pairs xs y)))))
(assert (forall ((y list)) (= (bmerge nil y) nil)))
(assert
  (forall ((z Nat) (x2 list))
    (= (bmerge (cons z x2) nil) (cons z x2))))
(assert
  (forall ((z Nat) (x3 Nat) (x4 list) (fail list) (x7 Nat) (x8 list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z (cons x7 x8))) (evens (cons x3 x4)))
          (bmerge (odds (cons z (cons x7 x8))) (odds (cons x3 x4)))))
      (= (bmerge (cons z (cons x7 x8)) (cons x3 x4)) fail))))
(assert
  (forall ((z Nat) (x3 Nat) (fail list))
    (=>
      (= fail
        (stitch (bmerge (evens (cons z nil)) (evens (cons x3 nil)))
          (bmerge (odds (cons z nil)) (odds (cons x3 nil)))))
      (= (bmerge (cons z nil) (cons x3 nil)) (sort2 z x3)))))
(assert
  (forall ((z Nat) (x3 Nat) (fail list) (x5 Nat) (x6 list))
    (=>
      (= fail
        (stitch
          (bmerge (evens (cons z nil)) (evens (cons x3 (cons x5 x6))))
          (bmerge (odds (cons z nil)) (odds (cons x3 (cons x5 x6))))))
      (= (bmerge (cons z nil) (cons x3 (cons x5 x6))) fail))))
(assert (forall ((y Nat)) (= (bsort (cons y nil)) (cons y nil))))
(assert
  (forall ((y Nat) (x2 Nat) (x3 list))
    (= (bsort (cons y (cons x2 x3)))
      (bmerge (bsort (evens (cons y (cons x2 x3))))
        (bsort (odds (cons y (cons x2 x3))))))))
(assert (= (evens nil) nil))
(assert
  (forall ((y Nat) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert (= (odds nil) nil))
(assert
  (forall ((y Nat) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert (forall ((x Nat)) (= (count x nil) zero)))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Nat) (z Nat) (ys list))
    (=> (= x z)
      (= (count x (cons z ys)) (plus (succ zero) (count x ys))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (not
    (forall ((x Nat) (xs list))
      (= (count x (bsort xs)) (count x xs)))))
(check-sat)
