
(declare-datatypes () ((Lst (cons (head Int) (tail Lst)) (nil))))
(declare-datatypes () ((Tree (node (data Int) (left Tree) (right Tree)) (leaf))))
(declare-datatypes () ((Pair (mkpair (first Int) (second Int)))
                       (ZLst (zcons (zhead Pair) (ztail ZLst)) (znil))))
(declare-fun less (Int Int) Bool)
(declare-fun plus (Int Int) Int)
(declare-fun mult (Int Int) Int)
(declare-fun qmult (Int Int Int) Int)
(declare-fun exp (Int Int) Int)
(declare-fun qexp (Int Int Int) Int)
(declare-fun fac (Int) Int)
(declare-fun qfac (Int Int) Int)
(declare-fun double (Int) Int)
(declare-fun half (Int) Int)
(declare-fun even (Int) Bool)
(declare-fun append (Lst Lst) Lst)
(declare-fun len (Lst) Int)
(declare-fun drop (Int Lst) Lst)
(declare-fun take (Int Lst) Lst)
(declare-fun count (Int Lst) Int)
(declare-fun mem (Int Lst) Bool)
(declare-fun rev (Lst) Lst)
(declare-fun qreva (Lst Lst) Lst)
(declare-fun insort (Int Lst) Lst)
(declare-fun sorted (Lst) Bool)
(declare-fun sort (Lst) Lst)
(declare-fun rotate (Int Lst) Lst)
(declare-fun revflat (Tree) Lst)
(declare-fun qrevaflat (Tree Lst) Lst)
(declare-fun lst-mem (Int (Set Int)) Bool)
(declare-fun lst-subset ((Set Int) (Set Int)) Bool)
(declare-fun lst-eq ((Set Int) (Set Int)) Bool)
(declare-fun lst-intersection ((Set Int) (Set Int)) (Set Int))
(declare-fun lst-union ((Set Int) (Set Int)) (Set Int))
(define-fun leq ((x Int) (y Int)) Bool (or (= x y) (less x y)))
(assert (forall ((n Int)) (=> (>= n 0) (= (plus 0 n) n))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus (+ 1 n) m) (+ 1 (plus n m))))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus n m) (+ n m)))))
(assert (forall ((n Int)) (= (mult 0 n) 0)))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (mult (+ 1 n) m) (plus (mult n m) m)))))
;(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (mult n m) (* n m)))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (>= (mult n m) 0))))
(assert (forall ((n Int)) (=> (>= n 0) (= (exp n 0) 1))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (exp n (+ 1 m)) (mult (exp n m) n)))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (>= (exp n m) 0))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (qexp n 0 m) m))))
(assert (forall ((n Int) (m Int) (p Int)) (=> (and (>= n 0) (>= m 0) (>= p 0)) (= (qexp n (+ 1 m) p) (qexp n m (mult p n))))))
(assert (forall ((n Int) (m Int) (p Int)) (=> (and (>= n 0) (>= m 0) (>= p 0))  (>= (qexp n m p) 0))))

; sub-goals
(assert 
(forall ((x Int) (y Int) (z Int)) (=> (and (>= x 0) (>= y 0) (>= z 0)) (= (mult (exp x y) z) (qexp x y z)))) ; G86 
)

; conjecture
(assert (not 
(forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (exp x y) (qexp x y 1))))   ; G35 
))
(check-sat)
