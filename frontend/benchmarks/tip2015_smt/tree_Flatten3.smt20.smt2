(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(declare-fun flatten3 (Tree) list)
(declare-fun ++ (list list) list)
(declare-fun flatten0 (Tree) list)
(assert (= (flatten3 Nil) nil))
(assert
  (forall ((z sk) (r Tree))
    (= (flatten3 (Node Nil z r)) (cons z (flatten3 r)))))
(assert
  (forall ((z sk) (r Tree) (p Tree) (x2 sk) (q Tree))
    (= (flatten3 (Node (Node p x2 q) z r))
      (flatten3 (Node p x2 (Node q z r))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (= (flatten0 Nil) nil))
(assert
  (forall ((p Tree) (y sk) (q Tree))
    (= (flatten0 (Node p y q))
      (++ (flatten0 p) (++ (cons y nil) (flatten0 q))))))
(assert (not (forall ((p Tree)) (= (flatten3 p) (flatten0 p)))))
(check-sat)
