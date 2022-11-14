(declare-datatype Sign ((Pos) (Neg)))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype Integer ((P (proj1-P Nat)) (N (proj1-N Nat))))
(declare-fun toInteger (Sign Nat) Integer)
(declare-fun sign (Integer) Sign)
(declare-fun plus (Nat Nat) Nat)
(declare-fun times2 (Nat Nat) Nat)
(declare-fun opposite (Sign) Sign)
(declare-fun timesSign (Sign Sign) Sign)
(declare-fun absVal (Integer) Nat)
(declare-fun times (Integer Integer) Integer)
(declare-fun |-2| (Nat Nat) Integer)
(declare-fun plus2 (Integer Integer) Integer)
(assert (forall ((y Nat)) (= (toInteger Pos y) (P y))))
(assert (= (toInteger Neg zero) (P zero)))
(assert (forall ((z Nat)) (= (toInteger Neg (succ z)) (N z))))
(assert (forall ((y Nat)) (= (sign (P y)) Pos)))
(assert (forall ((z Nat)) (= (sign (N z)) Neg)))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (times2 zero y) zero)))
(assert
  (forall ((y Nat) (z Nat))
    (= (times2 (succ z) y) (plus y (times2 z y)))))
(assert (= (opposite Pos) Neg))
(assert (= (opposite Neg) Pos))
(assert (forall ((y Sign)) (= (timesSign Pos y) y)))
(assert (forall ((y Sign)) (= (timesSign Neg y) (opposite y))))
(assert (forall ((n Nat)) (= (absVal (P n)) n)))
(assert (forall ((m Nat)) (= (absVal (N m)) (plus (succ zero) m))))
(assert
  (forall ((x Integer) (y Integer))
    (= (times x y)
      (toInteger (timesSign (sign x) (sign y))
        (times2 (absVal x) (absVal y))))))
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
(assert
  (not
    (forall ((x Integer) (y Integer) (z Integer))
      (= (times x (plus2 y z)) (plus2 (times x y) (times x z))))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 x (times2 y z)) (times2 (times2 x y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (times2 x y) (times2 y x))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 x (plus y z)) (plus (times2 x y) (times2 x z)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 (plus x y) z) (plus (times2 x z) (times2 y z)))))
(assert (forall ((x Nat)) (= (times2 x (succ zero)) x)))
(assert (forall ((x Nat)) (= (times2 (succ zero) x) x)))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((x Nat)) (= (times2 x zero) zero)))
(assert (forall ((x Nat)) (= (times2 zero x) zero)))
