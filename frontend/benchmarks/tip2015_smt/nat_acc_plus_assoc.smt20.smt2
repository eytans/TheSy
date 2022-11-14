(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun acc_plus (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (acc_plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat))
    (= (acc_plus (succ z) y) (acc_plus z (succ y)))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (= (acc_plus x (acc_plus y z)) (acc_plus (acc_plus x y) z)))))
(check-sat)
