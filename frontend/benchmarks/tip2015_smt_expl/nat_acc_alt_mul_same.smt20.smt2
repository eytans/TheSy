(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun times (Nat Nat) Nat)
(declare-fun acc_plus (Nat Nat) Nat)
(declare-fun acc_alt_mul (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (times zero y) zero)))
(assert
  (forall ((y Nat) (z Nat))
    (= (times (succ z) y) (plus y (times z y)))))
(assert (forall ((y Nat)) (= (acc_plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (acc_plus (succ z) y) (acc_plus z (succ y)))))
(assert (forall ((y Nat)) (= (acc_alt_mul zero y) zero)))
(assert (forall ((z Nat)) (= (acc_alt_mul (succ z) zero) zero)))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (acc_alt_mul (succ z) (succ x2))
      (acc_plus (succ z) (acc_plus x2 (acc_alt_mul z x2))))))
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
