(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun leq (Nat Nat) Bool)
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat))
      (let
        ((y2 (ite (leq y z) y z))
         (x2 (ite (leq x y) x y)))
        (= (ite (leq x y2) x y2) (ite (leq x2 z) x2 z))))))
(check-sat)
