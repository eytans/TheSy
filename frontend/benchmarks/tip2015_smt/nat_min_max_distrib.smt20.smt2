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
         (x2 (ite (leq x y) y x))
         (y3 (ite (leq x z) z x)))
        (= (ite (leq x y2) y2 x) (ite (leq x2 y3) x2 y3))))))
(check-sat)
