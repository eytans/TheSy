(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun take (Nat list) list)
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun length (list) Nat)
(declare-fun go (Nat Nat Nat) Nat)
(declare-fun mod_structural (Nat Nat) Nat)
(declare-fun drop (Nat list) list)
(declare-fun ++ (list list) list)
(declare-fun rotate (Nat list) list)
(assert
  (forall ((x Nat) (y Nat) (z Nat))
    (= (plus x (plus y z)) (plus (plus x y) z))))
(assert (forall ((x Nat) (y Nat)) (= (plus x y) (plus y x))))
(assert (forall ((x Nat)) (= (plus x zero) x)))
(assert (forall ((x Nat)) (= (plus zero x) x)))
(assert (forall ((y Nat)) (= (plus zero y) y)))
(assert
  (forall ((y Nat) (z Nat)) (= (plus (succ z) y) (succ (plus z y)))))
(assert (forall ((y Nat)) (= (minus zero y) zero)))
(assert (forall ((z Nat)) (= (minus (succ z) zero) zero)))
(assert
  (forall ((z Nat) (y2 Nat))
    (= (minus (succ z) (succ y2)) (minus z y2))))
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
(assert (forall ((y list)) (= (take zero y) nil)))
(assert (forall ((z Nat)) (= (take (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 sk) (xs list))
    (= (take (succ z) (cons z2 xs)) (cons z2 (take z xs)))))
(assert (= (length nil) zero))
(assert
  (forall ((y sk) (l list))
    (= (length (cons y l)) (plus (succ zero) (length l)))))
(assert (forall ((y list)) (= (drop zero y) y)))
(assert (forall ((z Nat)) (= (drop (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list))
    (= (drop (succ z) (cons z2 xs1)) (drop z xs1))))
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y list)) (= (rotate zero y) y)))
(assert (forall ((z Nat)) (= (rotate (succ z) nil) nil)))
(assert
  (forall ((z Nat) (z2 sk) (xs1 list))
    (= (rotate (succ z) (cons z2 xs1))
      (rotate z (++ xs1 (cons z2 nil))))))
