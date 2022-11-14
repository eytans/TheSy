(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list3 ((nil3) (cons3 (head3 sk) (tail3 list3))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Nat) (proj3-Node Heap))
   (Nil)))
(declare-datatype
  list2 ((nil2) (cons2 (head2 Heap) (tail2 list2))))
(declare-fun toHeap (list) list2)
(declare-fun leq (Nat Nat) Bool)
(declare-fun ordered (list) Bool)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun hpairwise (list2) list2)
(declare-fun hmerging (list2) Heap)
(declare-fun toHeap2 (list) Heap)
(declare-fun toList (Heap) list)
(declare-fun hsort (list) list)
(assert (= (toHeap nil) nil2))
(assert (ordered nil))
(assert (= (hpairwise nil2) nil2))
(assert (= (hmerging nil2) Nil))
(assert (= (toList Nil) nil))
(assert
  (forall ((y Nat) (z list))
    (= (toHeap (cons y z)) (cons2 (Node Nil y Nil) (toHeap z)))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((y Nat)) (ordered (cons y nil))))
(assert
  (forall ((y Nat) (y2 Nat) (xs list))
    (= (ordered (cons y (cons y2 xs)))
      (and (leq y y2) (ordered (cons y2 xs))))))
(assert (forall ((y Heap)) (= (hmerge Nil y) y)))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap))
    (= (hmerge (Node z x2 x3) Nil) (Node z x2 x3))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (not (leq x2 x5))
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge (Node z x2 x3) x6) x5 x4)))))
(assert
  (forall ((z Heap) (x2 Nat) (x3 Heap) (x4 Heap) (x5 Nat) (x6 Heap))
    (=> (leq x2 x5)
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge x3 (Node x4 x5 x6)) x2 z)))))
(assert
  (forall ((q Heap)) (= (hpairwise (cons2 q nil2)) (cons2 q nil2))))
(assert
  (forall ((q Heap) (r Heap) (qs list2))
    (= (hpairwise (cons2 q (cons2 r qs)))
      (cons2 (hmerge q r) (hpairwise qs)))))
(assert (forall ((q Heap)) (= (hmerging (cons2 q nil2)) q)))
(assert
  (forall ((q Heap) (z Heap) (x2 list2))
    (= (hmerging (cons2 q (cons2 z x2)))
      (hmerging (hpairwise (cons2 q (cons2 z x2)))))))
(assert (forall ((x list)) (= (toHeap2 x) (hmerging (toHeap x)))))
(assert
  (forall ((q Heap) (y Nat) (r Heap))
    (= (toList (Node q y r)) (cons y (toList (hmerge q r))))))
(assert (forall ((x list)) (= (hsort x) (toList (toHeap2 x)))))
