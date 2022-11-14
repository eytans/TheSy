(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun leq (Nat Nat) Bool)
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((y Nat)) (leq zero y)))
(assert (forall ((z Nat)) (not (leq (succ z) zero))))
(assert
  (forall ((z Nat) (x2 Nat))
    (= (leq (succ z) (succ x2)) (leq z x2))))
(assert
  (not
    (forall ((x Nat) (y Nat))
      (=> (leq x y) (=> (distinct x y) (lt x y))))))
(check-sat)
