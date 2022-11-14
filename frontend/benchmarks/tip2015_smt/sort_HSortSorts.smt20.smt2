(declare-datatype list2 ((nil2) (cons2 (head2 Int) (tail2 list2))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-datatype list ((nil) (cons (head Heap) (tail list))))
(declare-fun toHeap (list2) list)
(declare-fun ordered (list2) Bool)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun hpairwise (list) list)
(declare-fun hmerging (list) Heap)
(declare-fun toHeap2 (list2) Heap)
(declare-fun toList (Heap) list2)
(declare-fun hsort (list2) list2)
(assert (= (toHeap nil2) nil))
(assert (ordered nil2))
(assert (= (hpairwise nil) nil))
(assert (= (hmerging nil) Nil))
(assert (= (toList Nil) nil2))
(assert
  (forall ((y Int) (z list2))
    (= (toHeap (cons2 y z)) (cons (Node Nil y Nil) (toHeap z)))))
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
(assert (forall ((x list2)) (= (toHeap2 x) (hmerging (toHeap x)))))
(assert
  (forall ((p Heap) (y Int) (q Heap))
    (= (toList (Node p y q)) (cons2 y (toList (hmerge p q))))))
(assert (forall ((x list2)) (= (hsort x) (toList (toHeap2 x)))))
(assert (not (forall ((xs list2)) (ordered (hsort xs)))))
(check-sat)
