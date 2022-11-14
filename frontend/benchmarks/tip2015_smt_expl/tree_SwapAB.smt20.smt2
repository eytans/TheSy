(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Tree2
  ((Node2 (proj1-Node2 Tree2) (proj2-Node2 Int) (proj3-Node2 Tree2))
   (Nil2)))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(declare-fun swap (Int Int Tree2) Tree2)
(declare-fun elem (sk list) Bool)
(declare-fun ++ (list list) list)
(declare-fun flatten0 (Tree) list)
(assert (forall ((x Int) (y Int)) (= (swap x y Nil2) Nil2)))
(assert
  (forall ((x Int) (y Int) (p Tree2) (x2 Int) (q Tree2))
    (=> (distinct x2 x)
      (=> (distinct x2 y)
        (= (swap x y (Node2 p x2 q))
          (Node2 (swap x y p) x2 (swap x y q)))))))
(assert
  (forall ((x Int) (y Int) (p Tree2) (x2 Int) (q Tree2))
    (=> (distinct x2 x)
      (=> (= x2 y)
        (= (swap x y (Node2 p x2 q))
          (Node2 (swap x y p) x (swap x y q)))))))
(assert
  (forall ((x Int) (y Int) (p Tree2) (x2 Int) (q Tree2))
    (=> (= x2 x)
      (= (swap x y (Node2 p x2 q))
        (Node2 (swap x y p) y (swap x y q))))))
(assert (forall ((x sk)) (not (elem x nil))))
(assert
  (forall ((x sk) (z sk) (xs list))
    (= (elem x (cons z xs)) (or (= z x) (elem x xs)))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (= (flatten0 Nil) nil))
(assert
  (forall ((p Tree) (y sk) (q Tree))
    (= (flatten0 (Node p y q))
      (++ (flatten0 p) (++ (cons y nil) (flatten0 q))))))
