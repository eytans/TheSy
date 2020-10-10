;(set-logic ALL_SUPPORTED)

(declare-datatypes () ((Nat (succ (pred Nat)) (zero))))

(declare-fun plus (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (plus zero n) n)))
(assert (forall ((n Nat) (m Nat)) (= (plus (succ n) m) (succ (plus n m)))))

(declare-fun mult (Nat Nat) Nat)
(assert (forall ((n Nat)) (= (mult zero n) zero)))
(assert (forall ((n Nat) (m Nat)) (= (mult (succ n) m) (plus (mult n m) m))))

(declare-fun tri (Nat) Nat)
(assert (= (tri zero) zero))
(assert (forall ((n Nat)) (= (tri (succ n)) (plus (tri n) (succ n)))))

(declare-fun cubes (Nat) Nat)
(assert (= (cubes zero) zero))
(assert (forall ((n Nat)) (= (cubes (succ n)) (plus (cubes n) (mult (succ n) (mult (succ n) (succ n)))))))

; proven
(assert 
(forall ((n Nat) (m Nat)) (= (plus n m) (plus m n)))  ; G1 
)
(assert 
(forall ((x Nat) (y Nat) (z Nat)) (= (plus x (plus y z)) (plus (plus y x) z)))  ; G2 
)
(assert 
(forall ((n Nat) (m Nat)) (= (mult n m) (mult m n)))  ; G3 
)
(assert 
(forall ((x Nat) (y Nat) (z Nat)) (= (plus (mult x y) (mult x z)) (mult x (plus y z)))) ; G6 
)
(assert 
(forall ((x Nat)) (= (plus (tri x) (tri x)) (plus x (mult x x)))) ; G8 
)

; conjecture
(assert (not 
(forall ((x Nat)) (= (mult (tri x) (tri x)) (cubes x))) ; G9 
))
(check-sat)
