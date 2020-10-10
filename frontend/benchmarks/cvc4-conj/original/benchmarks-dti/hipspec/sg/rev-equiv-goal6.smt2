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
(forall ((x Lst) (y Lst) (z Lst)) (= (append (append x y) z) (append x (append y z))))  ; G2 
)
(assert  
(forall ((x Lst) (y Lst) (z Lst)) (= (qreva (qreva x y) z) (qreva y (append x z)))) ; G-rev-equiv-5 
)

; conjecture
(assert (not 
(forall ((x Lst) (y Lst) (z Lst)) (= (append (qreva x y) z) (qreva x (append y z))))  ; G-rev-equiv-6 
))
(check-sat)
