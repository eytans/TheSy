(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  Tree
  ((Leaf)
   (Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun mirror (Tree) Tree)
(declare-fun max (Nat Nat) Nat)
(declare-fun height (Tree) Nat)
(assert (forall ((y Nat)) (= (max Z y) y)))
(assert (forall ((z Nat)) (= (max (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (max (S z) (S x2)) (S (max z x2)))))
(assert (= (mirror Leaf) Leaf))
(assert
  (forall ((l Tree) (y sk) (r Tree))
    (= (mirror (Node l y r)) (Node (mirror r) y (mirror l)))))
(assert (= (height Leaf) Z))
(assert
  (forall ((l Tree) (y sk) (r Tree))
    (= (height (Node l y r)) (S (max (height l) (height r))))))
