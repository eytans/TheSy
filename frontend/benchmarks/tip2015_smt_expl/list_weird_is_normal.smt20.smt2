(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head list2) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun weird_concat (list) list2)
(declare-fun ++ (list2 list2) list2)
(declare-fun concat2 (list) list2)
(assert (= (weird_concat nil) nil2))
(assert
  (forall ((xss list))
    (= (weird_concat (cons nil2 xss)) (weird_concat xss))))
(assert
  (forall ((xss list) (z sk) (xs list2))
    (= (weird_concat (cons (cons2 z xs) xss))
      (cons2 z (weird_concat (cons xs xss))))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
(assert (= (concat2 nil) nil2))
(assert
  (forall ((y list2) (xs list))
    (= (concat2 (cons y xs)) (++ y (concat2 xs)))))
