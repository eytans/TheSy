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
        ((y2 (ite (leq y z) z y))
         (x2 (ite (leq x y) y x)))
        (= (ite (leq x y2) y2 x) (ite (leq x2 z) z x2))))))
(check-sat)
