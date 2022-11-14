(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun leq (Nat Nat) Bool)
(declare-fun geq (Nat Nat) Bool)
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert (forall ((x Nat) (y Nat)) (= (geq x y) (leq y x))))
(assert
  (not
    (forall ((x Nat) (y Nat)) (=> (geq x y) (=> (leq x y) (= x y))))))
(check-sat)
