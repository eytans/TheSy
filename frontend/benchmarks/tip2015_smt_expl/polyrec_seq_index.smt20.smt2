(declare-sort sk 0)
(declare-sort pair5 0)
(declare-sort Maybe3 0)
(declare-sort Seq2 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-sort fun13 0)
(declare-sort fun14 0)
(declare-sort fun15 0)
(declare-sort sk2 0)
(declare-datatype
  pair4 ((pair23 (proj1-pair3 sk) (proj2-pair3 sk))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Maybe2 ((Nothing2) (Just2 (proj1-Just2 sk))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 sk) (proj2-pair2 Maybe2))))
(declare-datatype list ((nil) (cons (head pair3) (tail list))))
(declare-datatype Maybe ((Nothing) (Just (proj1-Just pair3))))
(declare-datatype
  pair ((pair2 (proj1-pair pair3) (proj2-pair Maybe))))
(declare-datatype
  Seq ((Nil) (Cons (proj1-Cons pair) (proj2-Cons Seq2))))
(declare-datatype
  Seq3 ((Nil2) (Cons2 (proj1-Cons2 pair3) (proj2-Cons2 Seq))))
(declare-datatype
  Seq4 ((Nil3) (Cons3 (proj1-Cons3 sk) (proj2-Cons3 Seq3))))
(declare-fun pair32 (list2) list)
(declare-fun lookup (Int list2) Maybe2)
(declare-fun index (Int Seq3) Maybe)
(declare-fun index2 (Int Seq4) Maybe2)
(declare-fun fromList (list) Seq3)
(declare-fun fromList2 (list2) Seq4)
(declare-fun =<<< (fun12 Maybe2) Maybe2)
(declare-fun <$$> (fun1 Maybe2) Maybe2)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Maybe2)
(declare-fun apply13 (fun13 sk) sk2)
(declare-fun apply14 (fun14 sk2) sk)
(declare-fun apply15 (fun15 sk2) sk2)
(assert (= (pair32 nil2) nil))
(assert (= (fromList nil) Nil2))
(assert (= (fromList2 nil2) Nil3))
(assert
  (forall ((y sk))
    (= (pair32 (cons2 y nil2)) (cons (pair22 y Nothing2) nil))))
(assert
  (forall ((y sk) (y2 sk) (xs list2))
    (= (pair32 (cons2 y (cons2 y2 xs)))
      (cons (pair22 y (Just2 y2)) (pair32 xs)))))
(assert (forall ((x Int)) (= (lookup x nil2) Nothing2)))
(assert
  (forall ((x Int) (z sk) (x2 list2))
    (=> (= x 0) (= (lookup x (cons2 z x2)) (Just2 z)))))
(assert
  (forall ((x Int) (z sk) (x2 list2))
    (=> (distinct x 0)
      (= (lookup x (cons2 z x2)) (lookup (- x 1) x2)))))
(assert (forall ((x Int)) (= (index x Nil2) Nothing)))
(assert (forall ((x Int)) (= (index2 x Nil3) Nothing2)))
(assert
  (forall ((x Int) (z sk) (x2 Seq3))
    (=> (= x 0) (= (index2 x (Cons3 z x2)) (Just2 z)))))
(assert
  (forall ((x Int) (z sk) (x2 Seq3))
    (=> (distinct x 0)
      (=> (= (mod x 2) 0)
        (=> (= (index (div (- x 1) 2) x2) Nothing)
          (= (index2 x (Cons3 z x2)) Nothing2))))))
(assert
  (forall ((x Int) (z sk) (x2 Seq3))
    (=> (distinct x 0)
      (=> (distinct (mod x 2) 0)
        (=> (= (index (div (- x 1) 2) x2) Nothing)
          (= (index2 x (Cons3 z x2)) Nothing2))))))
(assert
  (forall ((x Int) (z sk) (x2 Seq3) (x6 sk) (y3 Maybe2))
    (=> (distinct x 0)
      (=> (= (mod x 2) 0)
        (=> (= (index (div (- x 1) 2) x2) (Just (pair22 x6 y3)))
          (= (index2 x (Cons3 z x2)) y3))))))
(assert
  (forall ((x Int) (z sk) (x2 Seq3) (x4 sk) (y2 Maybe2))
    (=> (distinct x 0)
      (=> (distinct (mod x 2) 0)
        (=> (= (index (div (- x 1) 2) x2) (Just (pair22 x4 y2)))
          (= (index2 x (Cons3 z x2)) (Just2 x4)))))))
(assert
  (forall ((x Int) (z pair3) (x2 Seq))
    (=> (= x 0) (= (index x (Cons2 z x2)) (Just z)))))
(assert
  (forall ((y sk) (xs list2))
    (= (fromList2 (cons2 y xs)) (Cons3 y (fromList (pair32 xs))))))
(assert (forall ((x fun12)) (= (=<<< x Nothing2) Nothing2)))
(assert
  (forall ((x fun12) (z sk)) (= (=<<< x (Just2 z)) (apply12 x z))))
(assert (forall ((x fun1)) (= (<$$> x Nothing2) Nothing2)))
(assert
  (forall ((x fun1) (z sk))
    (= (<$$> x (Just2 z)) (Just2 (apply1 x z)))))
