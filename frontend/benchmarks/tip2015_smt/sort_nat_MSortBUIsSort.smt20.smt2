(declare-sort fun1 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list2 ((nil2) (cons2 (head2 Nat) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun lmerge (list2 list2) list2)
(declare-fun pairwise (list) list)
(declare-fun mergingbu (list) list2)
(declare-fun msortbu (list2) list2)
(declare-fun insert2 (Nat list2) list2)
(declare-fun isort (list2) list2)
(declare-fun map2 (fun1 list2) list)
(declare-const lam fun1)
(declare-fun apply1 (fun1 Nat) list2)
(assert (= (pairwise nil) nil))
(assert (= (mergingbu nil) nil2))
(assert (= (isort nil2) nil2))
(assert (forall ((f fun1)) (= (map2 f nil2) nil)))
(assert
  (forall ((f fun1) (y Nat) (xs list2))
    (= (map2 f (cons2 y xs)) (cons (apply1 f y) (map2 f xs)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y list2)) (= (lmerge nil2 y) y)))
(assert
  (forall ((z Nat) (x2 list2))
    (= (lmerge (cons2 z x2) nil2) (cons2 z x2))))
(assert
  (forall ((z Nat) (x2 list2) (x3 Nat) (x4 list2))
    (=> (leq z x3)
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 z (lmerge x2 (cons2 x3 x4)))))))
(assert
  (forall ((z Nat) (x2 list2) (x3 Nat) (x4 list2))
    (=> (not (leq z x3))
      (= (lmerge (cons2 z x2) (cons2 x3 x4))
        (cons2 x3 (lmerge (cons2 z x2) x4))))))
(assert
  (forall ((xs list2)) (= (pairwise (cons xs nil)) (cons xs nil))))
(assert
  (forall ((xs list2) (ys list2) (xss list))
    (= (pairwise (cons xs (cons ys xss)))
      (cons (lmerge xs ys) (pairwise xss)))))
(assert (forall ((xs list2)) (= (mergingbu (cons xs nil)) xs)))
(assert
  (forall ((xs list2) (z list2) (x2 list))
    (= (mergingbu (cons xs (cons z x2)))
      (mergingbu (pairwise (cons xs (cons z x2)))))))
(assert
  (forall ((x list2)) (= (msortbu x) (mergingbu (map2 lam x)))))
(assert (forall ((x Nat)) (= (insert2 x nil2) (cons2 x nil2))))
(assert
  (forall ((x Nat) (z Nat) (xs list2))
    (=> (leq x z)
      (= (insert2 x (cons2 z xs)) (cons2 x (cons2 z xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list2))
    (=> (not (leq x z))
      (= (insert2 x (cons2 z xs)) (cons2 z (insert2 x xs))))))
(assert
  (forall ((y Nat) (xs list2))
    (= (isort (cons2 y xs)) (insert2 y (isort xs)))))
(assert (forall ((y Nat)) (= (apply1 lam y) (cons2 y nil2))))
(assert (not (forall ((xs list2)) (= (msortbu xs) (isort xs)))))
(check-sat)
