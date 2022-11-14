(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype
  Bin
  ((One) (ZeroAnd (proj1-ZeroAnd Bin)) (OneAnd (proj1-OneAnd Bin))))
(declare-fun s (Bin) Bin)
(declare-fun plus (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)
(assert (= (s One) (ZeroAnd One)))
(assert (forall ((xs Bin)) (= (s (ZeroAnd xs)) (OneAnd xs))))
(assert (forall ((ys Bin)) (= (s (OneAnd ys)) (ZeroAnd (s ys)))))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (= (toNat One) (succ zero)))
(assert
  (forall ((xs Bin))
    (= (toNat (ZeroAnd xs)) (plus (toNat xs) (toNat xs)))))
(assert
  (forall ((ys Bin))
    (= (toNat (OneAnd ys))
      (plus (plus (succ zero) (toNat ys)) (toNat ys)))))
(assert
  (not
    (forall ((n Bin)) (= (toNat (s n)) (plus (succ zero) (toNat n))))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
