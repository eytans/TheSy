(declare-sort sk 0)
(declare-datatype list4 ((nil4) (cons4 (head4 sk) (tail4 list4))))
(declare-datatype
  list3 ((nil2) (cons2 (head2 list4) (tail2 list3))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list2 ((nil3) (cons3 (head3 Nat) (tail3 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-fun weird_concat (list) list2)
(declare-fun weird_concat2 (list3) list4)
(declare-fun ++ (list4 list4) list4)
(declare-fun concat2 (list) list2)
(declare-fun concat3 (list3) list4)
(assert (= (weird_concat nil) nil3))
(assert (= (weird_concat2 nil2) nil4))
(assert
  (forall ((xss list))
    (= (weird_concat (cons nil3 xss)) (weird_concat xss))))
(assert
  (forall ((xss list3))
    (= (weird_concat2 (cons2 nil4 xss)) (weird_concat2 xss))))
(assert
  (forall ((xss list) (z Nat) (xs list2))
    (= (weird_concat (cons (cons3 z xs) xss))
      (cons3 z (weird_concat (cons xs xss))))))
(assert
  (forall ((xss list3) (z sk) (xs list4))
    (= (weird_concat2 (cons2 (cons4 z xs) xss))
      (cons4 z (weird_concat2 (cons2 xs xss))))))
(assert (forall ((y list4)) (= (++ nil4 y) y)))
(assert
  (forall ((y list4) (z sk) (xs list4))
    (= (++ (cons4 z xs) y) (cons4 z (++ xs y)))))
(assert (= (concat2 nil) nil3))
(assert (= (concat3 nil2) nil4))
(assert
  (forall ((y list4) (xs list3))
    (= (concat3 (cons2 y xs)) (++ y (concat3 xs)))))
(assert (not (forall ((x list)) (= (concat2 x) (weird_concat x)))))
(check-sat)
