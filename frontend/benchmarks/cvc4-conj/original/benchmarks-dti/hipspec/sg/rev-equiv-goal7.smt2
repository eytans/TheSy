;(set-logic ALL_SUPPORTED)

(declare-datatypes () ((Nat (succ (pred Nat)) (zero))
                       (Lst (cons (head Nat) (tail Lst)) (nil))))

(declare-fun append (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (append nil x) x)))
(assert (forall ((x Nat) (y Lst) (z Lst)) (= (append (cons x y) z) (cons x (append y z)))))

(declare-fun rev (Lst) Lst)
(assert (= (rev nil) nil))
(assert (forall ((x Nat) (y Lst)) (= (rev (cons x y)) (append (rev y) (cons x nil)))))

(declare-fun qreva (Lst Lst) Lst)
(assert (forall ((x Lst)) (= (qreva nil x) x)))
(assert (forall ((x Lst) (y Lst) (z Nat)) (= (qreva (cons z x) y) (qreva x (cons z y)))))

(declare-fun qrev (Lst) Lst)
(assert (forall ((x Lst)) (= (qrev x) (qreva x nil))))


; proven
(assert 
(forall ((x Lst)) (= (append x nil) x)) ; G1 
)
(assert 
(forall ((x Lst) (y Lst)) (= (append (rev x) (rev y)) (rev (append y x))))  ; G3 
)

(assert 
(forall ((x Lst) (y Lst) (z Lst)) (= (append (qreva x y) z) (qreva x (append y z))))  ; G6 
)
; conjecture
(assert (not 
(forall ((x Lst) (y Lst)) (= (qreva x (rev y)) (rev (append y x)))) ; G7 
))
(check-sat)
