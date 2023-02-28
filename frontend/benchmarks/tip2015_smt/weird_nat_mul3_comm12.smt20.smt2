(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun plus (Nat Nat) Nat)
(declare-fun add3 (Nat Nat Nat) Nat)
(declare-fun mul3 (Nat Nat Nat) Nat)
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((z Nat)) (= (add3 zero zero z) z)))
(assert
  (forall ((z Nat) (x3 Nat))
    (= (add3 zero (succ x3) z) (plus (succ zero) (add3 zero x3 z)))))
(assert
  (forall ((y Nat) (z Nat) (x2 Nat))
    (= (add3 (succ x2) y z) (plus (succ zero) (add3 x2 y z)))))
(assert (forall ((y Nat) (z Nat)) (= (mul3 zero y z) zero)))
(assert
  (forall ((z Nat) (x2 Nat)) (= (mul3 (succ x2) zero z) zero)))
(assert
  (forall ((x2 Nat) (x3 Nat))
    (= (mul3 (succ x2) (succ x3) zero) zero)))
(assert
  (forall ((x2 Nat) (x3 Nat) (x4 Nat) (fail Nat))
    (=>
      (= fail
        (plus (succ zero)
          (add3 (mul3 x2 x3 x4)
            (add3 (mul3 (succ zero) x3 x4)
              (mul3 x2 (succ zero) x4) (mul3 x2 x3 (succ zero)))
            (add3 x2 x3 x4))))
      (=> (= x2 zero)
        (=> (= x3 zero)
          (=> (= x4 zero)
            (= (mul3 (succ x2) (succ x3) (succ x4)) (succ zero))))))))
(assert
  (forall ((x2 Nat) (x3 Nat) (x4 Nat) (fail Nat))
    (=>
      (= fail
        (plus (succ zero)
          (add3 (mul3 x2 x3 x4)
            (add3 (mul3 (succ zero) x3 x4)
              (mul3 x2 (succ zero) x4) (mul3 x2 x3 (succ zero)))
            (add3 x2 x3 x4))))
      (=> (= x2 zero)
        (=> (= x3 zero)
          (=> (distinct x4 zero)
            (= (mul3 (succ x2) (succ x3) (succ x4)) fail)))))))
(assert
  (forall ((x2 Nat) (x3 Nat) (x4 Nat) (fail Nat))
    (=>
      (= fail
        (plus (succ zero)
          (add3 (mul3 x2 x3 x4)
            (add3 (mul3 (succ zero) x3 x4)
              (mul3 x2 (succ zero) x4) (mul3 x2 x3 (succ zero)))
            (add3 x2 x3 x4))))
      (=> (= x2 zero)
        (=> (distinct x3 zero)
          (= (mul3 (succ x2) (succ x3) (succ x4)) fail))))))
(assert
  (forall ((x2 Nat) (x3 Nat) (x4 Nat) (fail Nat))
    (=>
      (= fail
        (plus (succ zero)
          (add3 (mul3 x2 x3 x4)
            (add3 (mul3 (succ zero) x3 x4)
              (mul3 x2 (succ zero) x4) (mul3 x2 x3 (succ zero)))
            (add3 x2 x3 x4))))
      (=> (distinct x2 zero)
        (= (mul3 (succ x2) (succ x3) (succ x4)) fail)))))
(assert
  (not
    (forall ((x Nat) (y Nat) (z Nat)) (= (mul3 x y z) (mul3 y x z)))))
(check-sat)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))