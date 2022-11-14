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
(declare-fun plus (Nat Nat) Nat)
(declare-fun leq (Nat Nat) Bool)
(declare-fun hmerge (Heap Heap) Heap)
(declare-fun hpairwise (list2) list2)
(declare-fun hmerging (list2) Heap)
(declare-fun toHeap2 (list) Heap)
(declare-fun toList (Heap) list)
(declare-fun hsort (list) list)
(declare-fun count (sk list3) Nat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (= (toHeap nil) nil2))
(assert (= (hpairwise nil2) nil2))
(assert (= (hmerging nil2) Nil))
(assert (= (toList Nil) nil))
(assert
  (forall ((y Nat) (z list))
    (= (toHeap (cons y z)) (cons2 (Node Nil y Nil) (toHeap z)))))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
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
(assert (forall ((x sk)) (= (count x nil3) zero)))
(assert
  (forall ((x sk) (z sk) (ys list3))
    (=> (distinct x z) (= (count x (cons3 z ys)) (count x ys)))))
(assert
  (forall ((x sk) (z sk) (ys list3))
    (=> (= x z)
      (= (count x (cons3 z ys)) (plus (succ zero) (count x ys))))))
