(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 sk))))
(declare-datatype list ((nil2) (cons2 (head2 sk) (tail2 list))))
(declare-datatype pair ((pair2 (proj1-pair sk) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-fun select2 (sk list2) list2)
(declare-fun select22 (list) list2)
(declare-fun map2 (fun12 list2) list)
(declare-fun map3 (fun1 list) list)
(declare-const lam fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 pair) sk)
(assert (= (select22 nil2) nil))
(assert (forall ((x sk)) (= (select2 x nil) nil)))
(assert
  (forall ((x sk) (x2 list2) (y2 sk) (ys list))
    (= (select2 x (cons (pair2 y2 ys) x2))
      (cons (pair2 y2 (cons2 x ys)) (select2 x x2)))))
(assert
  (forall ((y sk) (xs list))
    (= (select22 (cons2 y xs))
      (cons (pair2 y xs) (select2 y (select22 xs))))))
(assert (forall ((f fun1)) (= (map3 f nil2) nil2)))
(assert
  (forall ((f fun1) (y sk) (xs list))
    (= (map3 f (cons2 y xs)) (cons2 (apply1 f y) (map3 f xs)))))
(assert (forall ((f fun12)) (= (map2 f nil) nil2)))
(assert
  (forall ((f fun12) (y pair) (xs list2))
    (= (map2 f (cons y xs)) (cons2 (apply12 f y) (map2 f xs)))))
(assert (forall ((x pair)) (= (apply12 lam x) (proj1-pair x))))
(assert (not (forall ((xs list)) (= (map2 lam (select22 xs)) xs))))
(check-sat)