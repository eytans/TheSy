(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype Integer ((P (proj1-P Nat)) (N (proj1-N Nat))))
(declare-const zero2 Integer)
(declare-fun plus (Nat Nat) Nat)
(declare-fun neg (Integer) Integer)
(declare-fun |-2| (Nat Nat) Integer)
(declare-fun plus2 (Integer Integer) Integer)
(assert (= zero2 (P zero)))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (= (neg (P zero)) (P zero)))
(assert (forall ((z Nat)) (= (neg (P (succ z))) (N z))))
(assert
  (forall ((n Nat)) (= (neg (N n)) (P (plus (succ zero) n)))))
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
  (forall ((m Nat) (n Nat)) (= (plus2 (P m) (P n)) (P (plus m n)))))
(assert
  (forall ((m Nat) (o Nat))
    (= (plus2 (P m) (N o)) (|-2| m (plus (succ zero) o)))))
(assert
  (forall ((m2 Nat) (n2 Nat))
    (= (plus2 (N m2) (P n2)) (|-2| n2 (plus (succ zero) m2)))))
(assert
  (forall ((m2 Nat) (n3 Nat))
    (= (plus2 (N m2) (N n3)) (N (plus (plus (succ zero) m2) n3)))))
(assert (not (forall ((x Integer)) (= (plus2 x (neg x)) zero2))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
