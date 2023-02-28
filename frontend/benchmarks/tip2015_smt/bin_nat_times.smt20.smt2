(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-datatype
  Bin
  ((One) (ZeroAnd (proj1-ZeroAnd Bin)) (OneAnd (proj1-OneAnd Bin))))
(declare-fun s (Bin) Bin)
(declare-fun plus2 (Bin Bin) Bin)
(declare-fun times (Bin Bin) Bin)
(declare-fun plus (Nat Nat) Nat)
(declare-fun times2 (Nat Nat) Nat)
(declare-fun toNat (Bin) Nat)
(assert (= (s One) (ZeroAnd One)))
(assert (forall ((xs Bin)) (= (s (ZeroAnd xs)) (OneAnd xs))))
(assert (forall ((ys Bin)) (= (s (OneAnd ys)) (ZeroAnd (s ys)))))
(assert (forall ((y Bin)) (= (plus2 One y) (s y))))
(assert
  (forall ((z Bin)) (= (plus2 (ZeroAnd z) One) (s (ZeroAnd z)))))
(assert
  (forall ((z Bin) (ys Bin))
    (= (plus2 (ZeroAnd z) (ZeroAnd ys)) (ZeroAnd (plus2 z ys)))))
(assert
  (forall ((z Bin) (xs Bin))
    (= (plus2 (ZeroAnd z) (OneAnd xs)) (OneAnd (plus2 z xs)))))
(assert
  (forall ((x2 Bin)) (= (plus2 (OneAnd x2) One) (s (OneAnd x2)))))
(assert
  (forall ((x2 Bin) (zs Bin))
    (= (plus2 (OneAnd x2) (ZeroAnd zs)) (OneAnd (plus2 x2 zs)))))
(assert
  (forall ((x2 Bin) (ys2 Bin))
    (= (plus2 (OneAnd x2) (OneAnd ys2)) (ZeroAnd (s (plus2 x2 ys2))))))
(assert (forall ((y Bin)) (= (times One y) y)))
(assert
  (forall ((y Bin) (xs1 Bin))
    (= (times (ZeroAnd xs1) y) (ZeroAnd (times xs1 y)))))
(assert
  (forall ((y Bin) (xs12 Bin))
    (= (times (OneAnd xs12) y) (plus2 (ZeroAnd (times xs12 y)) y))))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (times2 zero y) zero)))
(assert
  (forall ((y Nat) (z Nat))
    (= (times2 (succ z) y) (plus y (times2 z y)))))
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
    (forall ((x Bin) (y Bin))
      (= (toNat (times x y)) (times2 (toNat x) (toNat y))))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 x (times2 y z)) (times2 (times2 x y) z))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (times2 x y) (times2 y x))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 x (plus y z)) (plus (times2 x y) (times2 x z)))))
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (times2 (plus x y) z) (plus (times2 x z) (times2 y z)))))
(assert (forall ((x Nat)) (= (times2 x (succ zero)) x)))
(assert (forall ((x Nat)) (= (times2 (succ zero) x) x)))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((x Nat)) (= (times2 x zero) zero)))
(assert (forall ((x Nat)) (= (times2 zero x) zero)))