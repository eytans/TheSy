(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-datatype Nat ((Z) (S (proj1-S Nat))))
(declare-fun <=2 (Nat Nat) Bool)
(declare-fun len (list) Nat)
(declare-fun filter (fun12 list) list)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) Bool)
(assert (= (len nil) Z))
(assert
  (forall ((y sk) (xs list)) (= (len (cons y xs)) (S (len xs)))))
(assert (forall ((x fun12)) (= (filter x nil) nil)))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (apply12 x z)
      (= (filter x (cons z xs)) (cons z (filter x xs))))))
(assert
  (forall ((x fun12) (z sk) (xs list))
    (=> (not (apply12 x z)) (= (filter x (cons z xs)) (filter x xs)))))
(assert (forall ((y Nat)) (<=2 Z y)))
(assert (forall ((z Nat)) (not (<=2 (S z) Z))))
(assert
  (forall ((z Nat) (x2 Nat)) (= (<=2 (S z) (S x2)) (<=2 z x2))))
(assert
  (not
    (forall ((p fun12) (xs list)) (<=2 (len (filter p xs)) (len xs)))))
(check-sat)
