(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Nat) (proj3-TNode Tree))
   (TNil)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun insert2 (Nat list) list)
(declare-fun isort (list) list)
(declare-fun flatten (Tree list) list)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (= (isort nil) nil))
(assert (= (toTree nil) TNil))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((x Nat)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (not (leq x z))
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert
  (forall ((x Nat) (z Nat) (xs list))
    (=> (leq x z) (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((y Nat) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
(assert (forall ((y list)) (= (flatten TNil y) y)))
(assert
  (forall ((y list) (q Tree) (z Nat) (r Tree))
    (= (flatten (TNode q z r) y) (flatten q (cons z (flatten r y))))))
(assert (forall ((x Nat)) (= (add x TNil) (TNode TNil x TNil))))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (r Tree))
    (=> (not (leq x z))
      (= (add x (TNode q z r)) (TNode q z (add x r))))))
(assert
  (forall ((x Nat) (q Tree) (z Nat) (r Tree))
    (=> (leq x z) (= (add x (TNode q z r)) (TNode (add x q) z r)))))
(assert
  (forall ((y Nat) (xs list))
    (= (toTree (cons y xs)) (add y (toTree xs)))))
(assert (forall ((x list)) (= (tsort x) (flatten (toTree x) nil))))
