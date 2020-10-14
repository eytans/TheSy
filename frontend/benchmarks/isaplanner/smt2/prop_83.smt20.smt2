(declare-sort sk 0)
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype list ((nil) (cons (head pair) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun zip (list2 list2) list)
(declare-fun take (Nat list2) list2)
(declare-fun len (list2) Nat)
(declare-fun drop (Nat list2) list2)
(declare-fun ++ (list list) list)
(declare-fun ++2 (list2 list2) list2)
(assert (forall ((y list2)) (= (zip nil2 y) nil)))
(assert
  (forall ((z sk) (x2 list2)) (= (zip (cons2 z x2) nil2) nil)))
(assert
  (forall ((z sk) (x2 list2) (x3 sk) (x4 list2))
    (= (zip (cons2 z x2) (cons2 x3 x4))
      (cons (pair2 z x3) (zip x2 x4)))))
(assert (forall ((y list2)) (= (take Z y) nil2)))
(assert (forall ((z Nat)) (= (take (S z) nil2) nil2)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list2))
    (= (take (S z) (cons2 x2 x3)) (cons2 x2 (take z x3)))))
(assert (= (len nil2) Z))
(assert
  (forall ((y sk) (xs list2)) (= (len (cons2 y xs)) (S (len xs)))))
(assert (forall ((y list2)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil2) nil2)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list2))
    (= (drop (S z) (cons2 x2 x3)) (drop z x3))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert (forall ((y list2)) (= (++2 nil2 y) y)))
(assert
  (forall ((y list) (z pair) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert
  (forall ((y list2) (z sk) (xs list2))
    (= (++2 (cons2 z xs) y) (cons2 z (++2 xs y)))))
(assert
  (not
    (forall ((xs list2) (ys list2) (zs list2))
      (= (zip (++2 xs ys) zs)
        (++ (zip xs (take (len xs) zs)) (zip ys (drop (len xs) zs)))))))
(check-sat)
