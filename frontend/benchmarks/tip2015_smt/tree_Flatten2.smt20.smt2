(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Tree
  ((Node (proj1-Node Tree) (proj2-Node sk) (proj3-Node Tree)) (Nil)))
(declare-fun flatten2 (Tree list) list)
(declare-fun ++ (list list) list)
(declare-fun flatten0 (Tree) list)
(assert (forall ((y list)) (= (flatten2 Nil y) y)))
(assert
  (forall ((y list) (p Tree) (z sk) (q Tree))
    (= (flatten2 (Node p z q) y)
      (flatten2 p (cons z (flatten2 q y))))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (= (flatten0 Nil) nil))
(assert
  (forall ((p Tree) (y sk) (q Tree))
    (= (flatten0 (Node p y q))
      (++ (flatten0 p) (++ (cons y nil) (flatten0 q))))))
(assert
  (not (forall ((p Tree)) (= (flatten2 p nil) (flatten0 p)))))
(check-sat)
