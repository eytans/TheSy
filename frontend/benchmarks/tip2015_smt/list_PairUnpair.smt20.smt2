(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-fun unpair (list) list2)
(declare-fun pairs (list2) list)
(declare-fun length (list2) Int)
(assert (= (unpair nil) nil2))
(assert
  (forall ((xys list) (z sk) (y2 sk))
    (= (unpair (cons (pair2 z y2) xys))
      (cons2 z (cons2 y2 (unpair xys))))))
(assert (= (pairs nil2) nil))
(assert (forall ((y sk)) (= (pairs (cons2 y nil2)) nil)))
(assert
  (forall ((y sk) (y2 sk) (xs list2))
    (= (pairs (cons2 y (cons2 y2 xs)))
      (cons (pair2 y y2) (pairs xs)))))
(assert (= (length nil2) 0))
(assert
  (forall ((y sk) (l list2))
    (= (length (cons2 y l)) (+ 1 (length l)))))
(assert
  (not
    (forall ((xs list2))
      (=> (= (mod (length xs) 2) 0) (= (unpair (pairs xs)) xs)))))
(check-sat)
