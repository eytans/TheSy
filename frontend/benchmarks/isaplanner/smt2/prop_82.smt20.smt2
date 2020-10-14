(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun zip (list2 list2) list)
(declare-fun take (Nat list) list)
(declare-fun take2 (Nat list2) list2)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (pair2 z x3) (zip x2 x4)))))
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((y list2)) (= (take2 Z y) nil2)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert (forall ((z Nat)) (= (take2 (S z) nil2) nil2)))
(assert
  (forall ((z Nat) (x2 pair) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert
  (forall ((z Nat) (x2 sk) (x3 list2))
    (= (take2 (S z) (cons2 x2 x3)) (cons2 x2 (take2 z x3)))))
(assert
  (not
    (forall ((n Nat) (xs list2) (ys list2))
      (= (take n (zip xs ys)) (zip (take2 n xs) (take2 n ys))))))
(check-sat)
