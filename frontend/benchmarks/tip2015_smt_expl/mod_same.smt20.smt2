(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun minus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun mod2 (Nat Nat) Nat)
(declare-fun go (Nat Nat Nat) Nat)
(declare-fun mod_structural (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (minus zero y) zero)))
(assert (forall ((z Nat)) (= (minus (succ z) zero) zero)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (minus (succ z) (succ y2)) (minus z y2))))
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((x Nat)) (= (mod2 x zero) zero)))
(assert
  (forall ((x Nat) (z Nat))
    (=> (lt x (succ z)) (= (mod2 x (succ z)) x))))
(assert
  (forall ((x Nat) (z Nat))
    (=> (not (lt x (succ z)))
      (= (mod2 x (succ z)) (mod2 (minus x (succ z)) (succ z))))))
(assert (forall ((x Nat) (y Nat)) (= (go x y zero) zero)))
(assert (forall ((x2 Nat)) (= (go zero zero (succ x2)) zero)))
(assert
  (forall ((x2 Nat) (x5 Nat))
    (= (go zero (succ x5) (succ x2)) (minus (succ x2) (succ x5)))))
(assert
  (forall ((x2 Nat) (x3 Nat))
    (= (go (succ x3) zero (succ x2)) (go x3 x2 (succ x2)))))
(assert
  (forall ((x2 Nat) (x3 Nat) (x4 Nat))
    (= (go (succ x3) (succ x4) (succ x2)) (go x3 x4 (succ x2)))))
(assert
  (forall ((x Nat) (y Nat)) (= (mod_structural x y) (go x zero y))))
