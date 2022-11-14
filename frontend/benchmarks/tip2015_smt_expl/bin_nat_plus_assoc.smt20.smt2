(declare-sort sk 0)
(declare-sort sk2 0)
(declare-datatype
  Bin
  ((One) (ZeroAnd (proj1-ZeroAnd Bin)) (OneAnd (proj1-OneAnd Bin))))
(declare-fun s (Bin) Bin)
(declare-fun plus (Bin Bin) Bin)
(assert (= (s One) (ZeroAnd One)))
(assert (forall ((xs Bin)) (= (s (ZeroAnd xs)) (OneAnd xs))))
(assert (forall ((ys Bin)) (= (s (OneAnd ys)) (ZeroAnd (s ys)))))
(assert (forall ((y Bin)) (= (plus One y) (s y))))
(assert
  (forall ((z Bin)) (= (plus (ZeroAnd z) One) (s (ZeroAnd z)))))
(assert
  (forall ((z Bin) (ys Bin))
    (= (plus (ZeroAnd z) (ZeroAnd ys)) (ZeroAnd (plus z ys)))))
(assert
  (forall ((z Bin) (xs Bin))
    (= (plus (ZeroAnd z) (OneAnd xs)) (OneAnd (plus z xs)))))
(assert
  (forall ((x2 Bin)) (= (plus (OneAnd x2) One) (s (OneAnd x2)))))
(assert
  (forall ((x2 Bin) (zs Bin))
    (= (plus (OneAnd x2) (ZeroAnd zs)) (OneAnd (plus x2 zs)))))
(assert
  (forall ((x2 Bin) (ys2 Bin))
    (= (plus (OneAnd x2) (OneAnd ys2)) (ZeroAnd (s (plus x2 ys2))))))
