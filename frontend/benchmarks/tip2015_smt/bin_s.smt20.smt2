(declare-datatype
  Bin
  ((One) (ZeroAnd (proj1-ZeroAnd Bin)) (OneAnd (proj1-OneAnd Bin))))
(declare-fun toNat (Bin) Int)
(declare-fun s (Bin) Bin)
(assert (= (toNat One) 1))
(assert
  (forall ((xs Bin))
    (= (toNat (ZeroAnd xs)) (+ (toNat xs) (toNat xs)))))
(assert
  (forall ((ys Bin))
    (= (toNat (OneAnd ys)) (+ (+ 1 (toNat ys)) (toNat ys)))))
(assert (= (s One) (ZeroAnd One)))
(assert (forall ((xs Bin)) (= (s (ZeroAnd xs)) (OneAnd xs))))
(assert (forall ((ys Bin)) (= (s (OneAnd ys)) (ZeroAnd (s ys)))))
(assert (not (forall ((n Bin)) (= (toNat (s n)) (+ 1 (toNat n))))))
(check-sat)
