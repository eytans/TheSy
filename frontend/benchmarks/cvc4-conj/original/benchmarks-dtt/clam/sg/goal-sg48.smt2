
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
(assert (= (less 0 0) false))
(assert (forall ((x Int)) (=> (>= x 0) (= (less 0 (+ 1 x)) true))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less (+ 1 x) (+ 1 y)) (less x y)))))
(assert (forall ((x Int) (y Int)) (=> (and (>= x 0) (>= y 0)) (= (less x y) (< x y)))))
(assert (= (len nil) 0))
(assert (forall ((x Int) (y Lst)) (= (len (cons x y)) (+ 1 (len y)))))
(assert (forall ((x Lst)) (>= (len x) 0)))
(assert (forall ((i Int)) (= (insort i nil) (cons i nil))))
(assert (forall ((i Int) (x Int) (y Lst)) (= (insort i (cons x y)) (ite (less i x) (cons i (cons x y)) (cons x (insort i y))))))
(assert (= (sort nil) nil))
(assert (forall ((x Int) (y Lst)) (= (sort (cons x y)) (insort x (sort y)))))

; sub-goals
(assert 
(forall ((x Int) (y Lst)) (= (len (insort x y)) (+ 1 (len y))))  ; G68 
)

; conjecture
(assert (not 
(forall ((x Lst)) (= (len (sort x)) (len x))) ; G48 
))
(check-sat)
