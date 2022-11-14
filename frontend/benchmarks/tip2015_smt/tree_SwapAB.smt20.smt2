(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node Int) (proj3-Node Tree))
   (Nil)))
(declare-fun swap (Int Int Tree) Tree)
(declare-fun elem (Int list) Bool)
(declare-fun flatten0 (Tree) list)
(assert (forall ((x Int) (y Int)) (= (swap x y Nil) Nil)))
(assert
  (forall ((x Int) (y Int) (p Tree) (x2 Int) (q Tree))
    (=> (distinct x2 x)
      (=> (distinct x2 y)
        (= (swap x y (Node p x2 q))
          (Node (swap x y p) x2 (swap x y q)))))))
(assert
  (forall ((x Int) (y Int) (p Tree) (x2 Int) (q Tree))
    (=> (distinct x2 x)
      (=> (= x2 y)
        (= (swap x y (Node p x2 q)) (Node (swap x y p) x (swap x y q)))))))
(assert
  (forall ((x Int) (y Int) (p Tree) (x2 Int) (q Tree))
    (=> (= x2 x)
      (= (swap x y (Node p x2 q)) (Node (swap x y p) y (swap x y q))))))
(assert (forall ((x Int)) (not (elem x nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (= (flatten0 Nil) nil))
(assert
  (not
    (forall ((p Tree) (a Int) (b Int))
      (=> (elem a (flatten0 p))
        (=> (elem b (flatten0 p))
          (and (elem a (flatten0 (swap a b p)))
            (elem b (flatten0 (swap a b p)))))))))
(check-sat)
