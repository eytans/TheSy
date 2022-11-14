(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((zero) (succ (p Nat))))
(declare-fun take (Nat list) list)
(declare-fun plus (Nat Nat) Nat)
(declare-fun minus (Nat Nat) Nat)
(declare-fun lt (Nat Nat) Bool)
(declare-fun mod2 (Nat Nat) Nat)
(declare-fun length (list) Nat)
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
(assert (forall ((x Nat)) (not (lt x zero))))
(assert (forall ((z Nat)) (lt zero (succ z))))
(assert
  (forall ((z Nat) (n Nat)) (= (lt (succ n) (succ z)) (lt n z))))
(assert (forall ((x Nat)) (= (mod2 x zero) zero)))
(assert
  (forall ((x Nat) (z Nat))
    (=> (not (lt x (succ z)))
      (= (mod2 x (succ z)) (mod2 (minus x (succ z)) (succ z))))))
(assert
  (forall ((x Nat) (z Nat))
    (=> (lt x (succ z)) (= (mod2 x (succ z)) x))))
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
(assert
  (not
    (forall ((n Nat) (xs list))
      (= (rotate n xs)
        (++ (drop (mod2 n (length xs)) xs)
          (take (mod2 n (length xs)) xs))))))
(check-sat)
