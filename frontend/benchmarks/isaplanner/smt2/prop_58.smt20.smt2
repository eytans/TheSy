(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun zip (list2 list2) list)
(declare-fun drop (Nat list) list)
(declare-fun drop2 (Nat list2) list2)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (pair2 z x3) (zip x2 x4)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((y list2)) (= (drop2 Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert (forall ((z Nat)) (= (drop2 (S z) nil2) nil2)))
(assert
  (forall ((z Nat) (x2 pair) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert
  (forall ((z Nat) (x2 sk) (x3 list2))
    (= (drop2 (S z) (cons2 x2 x3)) (drop2 z x3))))
(assert
  (not
    (forall ((n Nat) (xs list2) (ys list2))
      (= (drop n (zip xs ys)) (zip (drop2 n xs) (drop2 n ys))))))
(check-sat)
