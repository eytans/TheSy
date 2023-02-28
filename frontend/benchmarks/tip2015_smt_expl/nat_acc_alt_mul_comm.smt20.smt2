(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun acc_plus (Nat Nat) Nat)
(declare-fun acc_alt_mul (Nat Nat) Nat)
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