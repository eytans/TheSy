(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun times (Nat Nat) Nat)
(declare-fun formula-pow3 (Nat Nat) Nat)
(declare-fun formula-pow2 (Nat Nat) Nat)
(declare-fun formula-pow (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (times zero y) zero)))
(assert
  (forall ((y Nat) (z Nat))
    (= (times (succ z) y) (plus y (times z y)))))
(assert (forall ((x Nat)) (= (formula-pow3 x zero) (succ zero))))
(assert
  (forall ((x Nat) (z Nat))
    (= (formula-pow3 x (succ z)) (times x (formula-pow3 x z)))))
(assert (forall ((x Nat)) (= (formula-pow2 x zero) (succ zero))))
(assert
  (forall ((x Nat) (z Nat))
    (= (formula-pow2 x (succ z)) (times x (formula-pow2 x z)))))
(assert (forall ((x Nat)) (= (formula-pow x zero) (succ zero))))
(assert
  (forall ((x Nat) (z Nat))
    (= (formula-pow x (succ z)) (times x (formula-pow x z)))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (formula-pow x (times y z))
        (formula-pow2 (formula-pow3 x y) z)))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (times y z)) (times (times x y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (times x y) (times y x))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times x (plus y z)) (plus (times x y) (times x z)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times (plus x y) z) (plus (times x z) (times y z)))))
(assert (forall ((x Nat)) (= (times x (succ zero)) x)))
(assert (forall ((x Nat)) (= (times (succ zero) x) x)))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((x Nat)) (= (times x zero) zero)))
(assert (forall ((x Nat)) (= (times zero x) zero)))
