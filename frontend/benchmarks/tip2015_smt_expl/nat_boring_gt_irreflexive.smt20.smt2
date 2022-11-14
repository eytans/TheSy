(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun lt (Nat Nat) Bool)
(declare-fun gt (Nat Nat) Bool)
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((x Nat) (y Nat)) (= (gt x y) (lt y x))))
