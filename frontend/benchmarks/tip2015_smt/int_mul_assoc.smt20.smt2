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
  (not
    (forall ((x Integer) (y Integer) (z Integer))
      (= (times x (times y z)) (times (times x y) z)))))
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