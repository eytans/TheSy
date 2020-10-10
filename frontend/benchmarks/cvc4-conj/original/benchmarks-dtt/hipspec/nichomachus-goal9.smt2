;(set-logic ALL_SUPPORTED)

(declare-fun plus (Int Int) Int)
(assert (forall ((n Int)) (=> (>= n 0) (= (plus 0 n) n))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus (+ 1 n) m) (+ 1 (plus n m))))))
; plus equivalent
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (plus n m) (+ n m)))))

(declare-fun mult (Int Int) Int)
(assert (forall ((n Int)) (=> (>= n 0) (= (mult 0 n) 0))))
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (mult (+ 1 n) m) (plus (mult n m) m)))))
; mult equivalent
;(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (= (mult n m) (* n m)))))
; since returns Nat, we can assume this lemma
(assert (forall ((n Int) (m Int)) (=> (and (>= n 0) (>= m 0)) (>= (mult n m) 0))))

(declare-fun tri (Int) Int)
(assert (= (tri 0) 0))
(assert (forall ((n Int)) (= (tri (+ 1 n)) (plus (tri n) (+ 1 n)))))
; since returns Nat, we can assume this lemma
(assert (forall ((n Int)) (=> (>= n 0) (>= (tri n) 0))))

(declare-fun cubes (Int) Int)
(assert (= (cubes 0) 0))
(assert (forall ((n Int)) (= (cubes (+ 1 n)) (plus (cubes n) (mult (+ 1 n) (mult (+ 1 n) (+ 1 n)))))))
; since returns Nat, we can assume this lemma
(assert (forall ((n Int)) (=> (>= n 0) (>= (cubes n) 0))))
; proven
; conjecture
(assert (not 
(forall ((x Int)) (=> (>= x 0) (= (mult (tri x) (tri x)) (cubes x)))) ; G-nichomachus-9 
))
(check-sat)
