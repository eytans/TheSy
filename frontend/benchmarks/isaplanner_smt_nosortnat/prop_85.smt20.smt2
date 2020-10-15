(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun zip (list2 list2) list)
(declare-fun len (list2) Nat)
(declare-fun ++ (list2 list2) list2)
(declare-fun rev (list2) list2)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (pair2 z x3) (zip x2 x4)))))
(assert (= (len nil2) Z))
(assert
  (forall ((y sk) (xs list2)) (= (len (cons2 y xs)) (S (len xs)))))
(assert (forall ((y list2)) (= (++ nil2 y) y)))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++ (cons2 z xs) y) (cons2 z (++ xs y)))))
(assert (= (rev nil2) nil2))
(assert
  (forall ((y sk) (xs list2))
    (= (rev (cons2 y xs)) (++ (rev xs) (cons2 y nil2)))))
