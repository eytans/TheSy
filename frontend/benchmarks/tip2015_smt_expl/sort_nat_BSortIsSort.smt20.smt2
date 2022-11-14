(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun sort2 (Nat Nat) list)
(declare-fun insert2 (Nat list) list)
(declare-fun isort (list) list)
(declare-fun evens (list) list)
(declare-fun evens2 (list2) list2)
(declare-fun odds (list) list)
(declare-fun odds2 (list2) list2)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(declare-fun pairs (list list) list)
(declare-fun stitch (list list) list)
(declare-fun bmerge (list list) list)
(declare-fun bsort (list) list)
(assert (= (isort nil) nil))
(assert (= (bsort nil) nil))
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
(assert (forall ((x Nat)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (leq x z))
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (leq x z) (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((y Nat) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
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
(assert (= (evens2 nil2) nil2))
(assert
  (forall ((y Nat) (xs list))
    (= (evens (cons y xs)) (cons y (odds xs)))))
(assert
  (forall ((y sk) (xs list2))
    (= (evens2 (cons2 y xs)) (cons2 y (odds2 xs)))))
(assert (= (odds nil) nil))
(assert (= (odds2 nil2) nil2))
(assert
  (forall ((y Nat) (xs list)) (= (odds (cons y xs)) (evens xs))))
(assert
  (forall ((y sk) (xs list2)) (= (odds2 (cons2 y xs)) (evens2 xs))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list) (z Nat) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
