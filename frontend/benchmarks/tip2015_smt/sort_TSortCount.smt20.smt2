(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Int) (proj3-TNode Tree))
   (TNil)))
(declare-fun flatten (Tree list) list)
(declare-fun count (Int list) Int)
(declare-fun add (Int Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (= (toTree nil) TNil))
(assert (forall ((y list)) (= (flatten TNil y) y)))
(assert
  (forall ((y list) (p Tree) (z Int) (q Tree))
    (= (flatten (TNode p z q) y) (flatten p (cons z (flatten q y))))))
(assert (forall ((x Int)) (= (add x TNil) (TNode TNil x TNil))))
(assert
  (forall ((x Int) (p Tree) (z Int) (q Tree))
    (=> (not (<= x z))
      (= (add x (TNode p z q)) (TNode p z (add x q))))))
(assert
  (forall ((x Int) (p Tree) (z Int) (q Tree))
    (=> (<= x z) (= (add x (TNode p z q)) (TNode (add x p) z q)))))
(assert
  (forall ((y Int) (xs list))
    (= (toTree (cons y xs)) (add y (toTree xs)))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
(assert (forall ((x Int)) (= (count x nil) 0)))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (distinct x z) (= (count x (cons z ys)) (count x ys)))))
(assert
  (forall ((x Int) (z Int) (ys list))
    (=> (= x z) (= (count x (cons z ys)) (+ 1 (count x ys))))))
(assert
  (not
    (forall ((x Int) (xs list))
      (= (count x (tsort xs)) (count x xs)))))
(check-sat)
