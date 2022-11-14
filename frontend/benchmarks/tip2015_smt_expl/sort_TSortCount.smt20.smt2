(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Int) (proj3-TNode Tree))
   (TNil)))
(declare-fun flatten (Tree list2) list2)
(declare-fun count (sk list) Int)
(declare-fun add (Int Tree) Tree)
(declare-fun toTree (list2) Tree)
(declare-fun tsort (list2) list2)
(assert (= (toTree nil2) TNil))
(assert (forall ((y list2)) (= (flatten TNil y) y)))
(assert
  (forall ((y list2) (p Tree) (z Int) (q Tree))
    (= (flatten (TNode p z q) y) (flatten p (cons2 z (flatten q y))))))
(assert (forall ((x Int)) (= (add x TNil) (TNode TNil x TNil))))
(assert
  (forall ((x Int) (p Tree) (z Int) (q Tree))
    (=> (not (<= x z))
      (= (add x (TNode p z q)) (TNode p z (add x q))))))
(assert
  (forall ((x Int) (p Tree) (z Int) (q Tree))
    (=> (<= x z) (= (add x (TNode p z q)) (TNode (add x p) z q)))))
(assert
  (forall ((y Int) (xs list2))
    (= (toTree (cons2 y xs)) (add y (toTree xs)))))
(assert
  (forall ((x list2)) (= (tsort x) (flatten (toTree x) nil2))))
(assert (forall ((x sk)) (= (count x nil) 0)))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
