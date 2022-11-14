(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun op (Nat Nat Nat Nat) Nat)
(assert (forall ((y Nat) (x2 Nat)) (= (op zero y zero x2) x2)))
(assert
  (forall ((y Nat) (x2 Nat) (x4 Nat))
    (= (op (succ x4) y zero x2) (op x4 y y x2))))
(assert
  (forall ((x Nat) (y Nat) (x2 Nat) (x3 Nat))
    (= (op x y (succ x3) x2) (op x y x3 (succ x2)))))
(assert
  (not
    (forall ((a Nat) (b Nat) (c Nat) (d Nat))
      (= (op a b c d) (op b a d c)))))
(check-sat)
