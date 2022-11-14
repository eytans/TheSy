(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype
  Tree
  ((TNode (proj1-TNode Tree) (proj2-TNode Nat) (proj3-TNode Tree))
   (TNil)))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun flatten (Tree list) list)
(declare-fun isPermutation (list list) Bool)
(declare-fun add (Nat Tree) Tree)
(declare-fun toTree (list) Tree)
(declare-fun tsort (list) list)
(assert (= (toTree nil) TNil))
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
(assert (isPermutation nil nil))
(assert
  (forall ((z Nat) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (not (forall ((xs list)) (isPermutation (tsort xs) xs))))
(check-sat)
