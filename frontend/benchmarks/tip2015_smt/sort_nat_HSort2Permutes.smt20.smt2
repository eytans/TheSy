(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype list ((nil) (cons (head Nat) (tail list))))
(declare-datatype
  Heap
  ((Node (proj1-Node Heap) (proj2-Node Nat) (proj3-Node Heap))
   (Nil)))
(declare-fun leq (Nat Nat) Bool)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun toList (Heap) list)
(declare-fun hinsert (Nat Heap) Heap)
(declare-fun toHeap2 (list) Heap)
(declare-fun hsort2 (list) list)
(declare-fun isPermutation (list list) Bool)
(assert (= (toList Nil) nil))
(assert (= (toHeap2 nil) Nil))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
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
  (forall ((q Heap) (y Nat) (r Heap))
    (= (toList (Node q y r)) (cons y (toList (hmerge q r))))))
(assert
  (forall ((x Nat) (y Heap))
    (= (hinsert x y) (hmerge (Node Nil x Nil) y))))
(assert
  (forall ((y Nat) (xs list))
    (= (toHeap2 (cons y xs)) (hinsert y (toHeap2 xs)))))
(assert (forall ((x list)) (= (hsort2 x) (toList (toHeap2 x)))))
(assert (isPermutation nil nil))
(assert
  (forall ((z Nat) (x2 list)) (not (isPermutation nil (cons z x2)))))
(assert (not (forall ((xs list)) (isPermutation (hsort2 xs) xs))))
(check-sat)
