(declare-datatype list ((nil) (cons (head Int) (tail list))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Int) (proj3-Node Heap))
   (Nil)))
(declare-fun insert2 (Int list) list)
(declare-fun isort (list) list)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun toList (Heap) list)
(declare-fun hinsert (Int Heap) Heap)
(declare-fun toHeap2 (list) Heap)
(declare-fun hsort2 (list) list)
(assert (= (isort nil) nil))
(assert (= (toList Nil) nil))
(assert (= (toHeap2 nil) Nil))
(assert (forall ((x Int)) (= (insert2 x nil) (cons x nil))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (not (<= x z))
      (= (insert2 x (cons z xs)) (cons z (insert2 x xs))))))
(assert
  (forall ((x Int) (z Int) (xs list))
    (=> (<= x z) (= (insert2 x (cons z xs)) (cons x (cons z xs))))))
(assert
  (forall ((y Int) (xs list))
    (= (isort (cons y xs)) (insert2 y (isort xs)))))
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
    (= (toList (Node p y q)) (cons y (toList (hmerge p q))))))
(assert
  (forall ((x Int) (y Heap))
    (= (hinsert x y) (hmerge (Node Nil x Nil) y))))
(assert
  (forall ((y Int) (xs list))
    (= (toHeap2 (cons y xs)) (hinsert y (toHeap2 xs)))))
(assert (forall ((x list)) (= (hsort2 x) (toList (toHeap2 x)))))
(assert (not (forall ((xs list)) (= (hsort2 xs) (isort xs)))))
(check-sat)