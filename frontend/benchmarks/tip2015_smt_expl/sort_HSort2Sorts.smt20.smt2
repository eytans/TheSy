(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-fun ordered (list2) Bool)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun toList (Heap) list2)
(declare-fun hinsert (Int Heap) Heap)
(declare-fun toHeap2 (list2) Heap)
(declare-fun hsort2 (list2) list2)
(assert (ordered nil2))
(assert (= (toList Nil) nil2))
(assert (= (toHeap2 nil2) Nil))
(assert (forall ((y Int)) (ordered (cons2 y nil2))))
(assert
  (forall ((y Int) (y2 Int) (xs list2))
    (= (ordered (cons2 y (cons2 y2 xs)))
      (and (<= y y2) (ordered (cons2 y2 xs))))))
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
  (forall ((p Heap) (y Int) (q Heap))
    (= (toList (Node p y q)) (cons2 y (toList (hmerge p q))))))
(assert
  (forall ((x Int) (y Heap))
    (= (hinsert x y) (hmerge (Node Nil x Nil) y))))
(assert
  (forall ((y Int) (xs list2))
    (= (toHeap2 (cons2 y xs)) (hinsert y (toHeap2 xs)))))
(assert (forall ((x list2)) (= (hsort2 x) (toList (toHeap2 x)))))
