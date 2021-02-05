;(set-logic ALL_SUPPORTED)

(declare-datatypes () ((Nat (succ (pred Nat)) (zero))
                       (Lst (cons (head Nat) (tail Lst)) (nil))))

(declare-fun len (Lst) Nat)
(assert (= (len nil) zero))
(assert (forall ((x Nat) (y Lst)) (= (len (cons x y)) (succ (len y)))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rotate (Nat Lst) Lst)
(assert (forall ((x Lst)) (= (rotate zero x) x)))
(assert (forall ((n Nat)) (= (rotate (succ n) nil) nil)))
(assert (forall ((n Nat) (y Nat) (x Lst)) (= (rotate (succ n) (cons y x)) (rotate n (append x (cons y nil))))))

(declare-fun plus (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (plus zero n) n)))
(assert (forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m)))))











; proven
; conjecture
(assert (not 
(forall ((n Nat) (m Nat) (x Lst)) (= (rotate (succ n) (rotate m x)) (rotate (succ m) (rotate n x))))  ; G-rotate-4 
))
(check-sat)
