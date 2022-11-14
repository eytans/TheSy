(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Nat) (proj3-TNode Tree))
   (TNil)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun count (sk list2) Nat)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (toTree nil) TNil))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
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
(assert (forall ((x sk)) (= (count x nil2) zero)))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (distinct x z) (= (count x (cons2 z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (= x z)
      (= (count x (cons2 z ys)) (plus (succ zero) (count x ys))))))
