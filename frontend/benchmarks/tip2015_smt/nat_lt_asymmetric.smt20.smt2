(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun lt (Nat Nat) Bool)
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert
  (not (forall ((x Nat) (y Nat)) (=> (lt x y) (not (lt y x))))))
(check-sat)