;(set-logic ALL_SUPPORTED)

(declare-datatypes () ((Lst (cons (head Nat) (tail Lst)) (nil))
                       (Nat (succ (pred Nat)) (zero))))

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

; mapping to integers
(declare-fun nat-to-int (Nat) Int)
; it is an injection to positive integers
(assert (forall ((x Nat)) (>= (nat-to-int x) 0)))
(assert (forall ((x Nat) (y Nat)) (=> (= (nat-to-int x) (nat-to-int y)) (= x y))))
; mapping for functions
(assert (= (nat-to-int zero) 0))
(assert (forall ((x Nat)) (= (nat-to-int (succ x)) (+ 1 (nat-to-int x)))))
(assert (forall ((x Nat) (y Nat)) (= (nat-to-int (plus x y)) (+ (nat-to-int x) (nat-to-int y)))))










; proven
; conjecture
(assert (not 
(forall ((x Lst)) (= (rotate (len x) x) x))  ; G-rotate-9 
))
(check-sat)
