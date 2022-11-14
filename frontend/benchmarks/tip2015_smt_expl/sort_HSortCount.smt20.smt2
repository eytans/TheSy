(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list3 ((nil3) (cons3 (head3 Int) (tail3 list3))))
(declare-datatype list2 ((nil2) (cons2 (head2 sk) (tail2 list2))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-datatype list ((nil) (cons (head Heap) (tail list))))
(declare-fun toHeap (list3) list)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun hpairwise (list) list)
(declare-fun hmerging (list) Heap)
(declare-fun toHeap2 (list3) Heap)
(declare-fun toList (Heap) list3)
(declare-fun hsort (list3) list3)
(declare-fun count (sk list2) Int)
(assert (= (toHeap nil3) nil))
(assert (= (hpairwise nil) nil))
(assert (= (hmerging nil) Nil))
(assert (= (toList Nil) nil3))
(assert
  (forall ((y Int) (z list3))
    (= (toHeap (cons3 y z)) (cons (Node Nil y Nil) (toHeap z)))))
(assert (forall ((y Heap)) (= (hmerge Nil y) y)))
(assert
  (forall ((z Heap) (x2 Int) (x3 Heap))
    (= (hmerge (Node z x2 x3) Nil) (Node z x2 x3))))
(assert
  (forall ((z Heap) (x2 Int) (x3 Heap) (x4 Heap) (x5 Int) (x6 Heap))
    (=> (not (<= x2 x5))
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge (Node z x2 x3) x6) x5 x4)))))
(assert
  (forall ((z Heap) (x2 Int) (x3 Heap) (x4 Heap) (x5 Int) (x6 Heap))
    (=> (<= x2 x5)
      (= (hmerge (Node z x2 x3) (Node x4 x5 x6))
        (Node (hmerge x3 (Node x4 x5 x6)) x2 z)))))
(assert
  (forall ((p Heap)) (= (hpairwise (cons p nil)) (cons p nil))))
(assert
  (forall ((p Heap) (q Heap) (qs list))
    (= (hpairwise (cons p (cons q qs)))
      (cons (hmerge p q) (hpairwise qs)))))
(assert (forall ((p Heap)) (= (hmerging (cons p nil)) p)))
(assert
  (forall ((p Heap) (z Heap) (x2 list))
    (= (hmerging (cons p (cons z x2)))
      (hmerging (hpairwise (cons p (cons z x2)))))))
(assert (forall ((x list3)) (= (toHeap2 x) (hmerging (toHeap x)))))
(assert
  (forall ((p Heap) (y Int) (q Heap))
    (= (toList (Node p y q)) (cons3 y (toList (hmerge p q))))))
(assert (forall ((x list3)) (= (hsort x) (toList (toHeap2 x)))))
(assert (forall ((x sk)) (= (count x nil2) 0)))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (distinct x z) (= (count x (cons2 z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list2))
    (=> (= x z) (= (count x (cons2 z ys)) (+ 1 (count x ys))))))
