(declare-sort sk 0)
(declare-sort fun1 0)
(declare-sort fun12 0)
(declare-datatype list ((nil) (cons (head sk) (tail list))))
(declare-fun ++ (list list) list)
(declare-fun >>= (list fun12) list)
(declare-fun lam (fun12 fun12) fun12)
(declare-fun apply1 (fun1 sk) sk)
(declare-fun apply12 (fun12 sk) list)
(assert (forall ((y list)) (= (++ nil y) y)))
(assert
  (forall ((y list) (z sk) (xs list))
    (= (++ (cons z xs) y) (cons z (++ xs y)))))
(assert (forall ((y fun12)) (= (>>= nil y) nil)))
(assert
  (forall ((y fun12) (z sk) (xs list))
    (= (>>= (cons z xs) y) (++ (apply12 y z) (>>= xs y)))))
(assert
  (forall ((f fun12) (g fun12) (x sk))
    (= (apply12 (lam f g) x) (>>= (apply12 f x) g))))
(assert
  (not
    (forall ((m list) (f fun12) (g fun12))
      (= (>>= (>>= m f) g) (>>= m (lam f g))))))
(check-sat)
