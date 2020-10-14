(declare-sort sk 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun take (Nat list) list)
(declare-fun drop (Nat list) list)
(declare-fun |-2| (Nat Nat) Nat)
(assert (forall ((y Nat)) (= (|-2| Z y) Z)))
(assert (forall ((z Nat)) (= (|-2| (S z) Z) (S z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (|-2| (S z) (S x2)) (|-2| z x2))))
(assert (forall ((y list)) (= (take Z y) nil)))
(assert (forall ((z Nat)) (= (take (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (take (S z) (cons x2 x3)) (cons x2 (take z x3)))))
(assert (forall ((y list)) (= (drop Z y) y)))
(assert (forall ((z Nat)) (= (drop (S z) nil) nil)))
(assert
  (forall ((z Nat) (x2 sk) (x3 list))
    (= (drop (S z) (cons x2 x3)) (drop z x3))))
(assert
  (not
    (forall ((n Nat) (m Nat) (xs list))
      (= (drop n (take m xs)) (take (|-2| m n) (drop n xs))))))
(check-sat)
