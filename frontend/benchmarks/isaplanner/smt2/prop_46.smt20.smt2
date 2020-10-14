(declare-sort sk 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list4 ((nil4) (cons4 (head4 sk) (tail4 list4))))
(declare-datatype
  list2 ((nil2) (cons2 (head2 pair3) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list3 ((nil3) (cons3 (head3 Nat) (tail3 list3))))
(declare-datatype pair ((pair2 (proj1-pair Nat) (proj2-pair sk))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-fun zip (list3 list4) list)
(declare-fun zip2 (list4 list4) list2)
(assert (forall ((y list4)) (= (zip nil3 y) nil)))
(assert (forall ((y list4)) (= (zip2 nil4 y) nil2)))
(assert
  (forall ((z Nat) (x2 list3)) (= (zip (cons3 z x2) nil4) nil)))
(assert
  (forall ((z sk) (x2 list4)) (= (zip2 (cons4 z x2) nil4) nil2)))
(assert
  (forall ((z Nat) (x2 list3) (x3 sk) (x4 list4))
    (= (zip (cons3 z x2) (cons4 x3 x4))
      (cons (pair2 z x3) (zip x2 x4)))))
(assert
  (forall ((z sk) (x2 list4) (x3 sk) (x4 list4))
    (= (zip2 (cons4 z x2) (cons4 x3 x4))
      (cons2 (pair22 z x3) (zip2 x2 x4)))))
(assert (not (forall ((xs list4)) (= (zip nil3 xs) nil))))
(check-sat)
