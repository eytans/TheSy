(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype Integer ((P (proj1-P Nat)) (N (proj1-N Nat))))
(declare-const zero2 Integer)
(declare-fun plus2 (Nat Nat) Nat)
(declare-fun |-2| (Nat Nat) Integer)
(declare-fun plus (Integer Integer) Integer)
(assert (= zero2 (P zero)))
(assert (forall ((y Nat)) (= (plus2 zero y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (plus2 (succ z) y) (succ (plus2 z y)))))
(assert
  (forall ((fail Integer))
    (=> (= fail (P zero)) (= (|-2| zero zero) (P zero)))))
(assert
  (forall ((fail Integer) (x4 Nat))
    (=> (= fail (N x4)) (= (|-2| zero (succ x4)) fail))))
(assert
  (forall ((y Nat) (fail Integer) (x3 Nat))
    (=> (= fail (ite (is-succ y) (|-2| x3 (p y)) (P (succ x3))))
      (= (|-2| (succ x3) y) fail))))
(assert
  (forall ((m Nat) (n Nat)) (= (plus (P m) (P n)) (P (plus2 m n)))))
(assert
  (forall ((m Nat) (o Nat))
    (= (plus (P m) (N o)) (|-2| m (plus2 (succ zero) o)))))
(assert
  (forall ((m2 Nat) (n2 Nat))
    (= (plus (N m2) (P n2)) (|-2| n2 (plus2 (succ zero) m2)))))
(assert
  (forall ((m2 Nat) (n3 Nat))
    (= (plus (N m2) (N n3)) (N (plus2 (plus2 (succ zero) m2) n3)))))
(assert (not (forall ((x Integer)) (= x (plus x zero2)))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus2 x (plus2 y z)) (plus2 (plus2 x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus2 x y) (plus2 y x))))
(assert (forall ((x Nat)) (= (plus2 x zero) x)))
(assert (forall ((x Nat)) (= (plus2 zero x) x)))
