(declare-datatype
  list3 ((nil3) (cons3 (head3 Bool) (tail3 list3))))
(declare-datatype A ((X) (Y)))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom A))
   (Plus (proj1-Plus R) (proj2-Plus R))
   (Seq (proj1-Seq R) (proj2-Seq R)) (Star (proj1-Star R))))
(declare-datatype list ((nil2) (cons2 (head2 A) (tail2 list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list2 ((nil) (cons (head pair) (tail list2))))
(declare-fun split2 (list) list2)
(declare-fun seq (R R) R)
(declare-fun plus (R R) R)
(declare-fun or2 (list3) Bool)
(declare-fun eqA (A A) Bool)
(declare-fun eps (R) Bool)
(declare-fun epsR (R) R)
(declare-fun step (R A) R)
(declare-fun recognise (R list) Bool)
(declare-fun formula (R R list2) list3)
(assert (not (or2 nil3)))
(assert (eqA X X))
(assert (not (eqA X Y)))
(assert (not (eqA Y X)))
(assert (eqA Y Y))
(assert (eps Eps))
(assert
  (forall ((x R))
    (=> (distinct x Nil) (=> (distinct x Eps) (= (seq x Eps) x)))))
(assert (forall ((x R)) (=> (distinct x Nil) (= (seq x Nil) Nil))))
(assert
  (forall ((x R) (y R))
    (=> (distinct x Nil)
      (=> (distinct y Nil)
        (=> (distinct x Eps)
          (=> (distinct y Eps) (= (seq x y) (Seq x y))))))))
(assert (forall ((y R)) (=> (distinct y Nil) (= (seq Eps y) y))))
(assert (forall ((y R)) (= (seq Nil y) Nil)))
(assert (forall ((x R)) (=> (distinct x Nil) (= (plus x Nil) x))))
(assert
  (forall ((x R) (y R))
    (=> (distinct x Nil)
      (=> (distinct y Nil) (= (plus x y) (Plus x y))))))
(assert (forall ((y R)) (= (plus Nil y) y)))
(assert
  (forall ((y Bool) (xs list3))
    (= (or2 (cons3 y xs)) (or y (or2 xs)))))
(assert
  (forall ((x R))
    (=> (distinct x Eps)
      (=> (distinct x (Plus (proj1-Plus x) (proj2-Plus x)))
        (=> (distinct x (Seq (proj1-Seq x) (proj2-Seq x)))
          (=> (distinct x (Star (proj1-Star x))) (not (eps x))))))))
(assert
  (forall ((p R) (q R)) (= (eps (Plus p q)) (or (eps p) (eps q)))))
(assert
  (forall ((r R) (q2 R))
    (= (eps (Seq r q2)) (and (eps r) (eps q2)))))
(assert (forall ((y R)) (eps (Star y))))
(assert (forall ((x R)) (=> (not (eps x)) (= (epsR x) Nil))))
(assert (forall ((x R)) (=> (eps x) (= (epsR x) Eps))))
(assert
  (forall ((x R) (y A))
    (=> (distinct x (Atom (proj1-Atom x)))
      (=> (distinct x (Plus (proj1-Plus x) (proj2-Plus x)))
        (=> (distinct x (Seq (proj1-Seq x) (proj2-Seq x)))
          (=> (distinct x (Star (proj1-Star x))) (= (step x y) Nil)))))))
(assert
  (forall ((y A) (a A))
    (=> (not (eqA a y)) (= (step (Atom a) y) Nil))))
(assert
  (forall ((y A) (a A)) (=> (eqA a y) (= (step (Atom a) y) Eps))))
(assert
  (forall ((y A) (p R) (q R))
    (= (step (Plus p q) y) (plus (step p y) (step q y)))))
(assert
  (forall ((y A) (r R) (q2 R))
    (= (step (Seq r q2) y)
      (plus (seq (step r y) q2) (seq (epsR r) (step q2 y))))))
(assert
  (forall ((y A) (p2 R))
    (= (step (Star p2) y) (seq (step p2 y) (Star p2)))))
(assert (forall ((x R)) (= (recognise x nil2) (eps x))))
(assert
  (forall ((x R) (z A) (xs list))
    (= (recognise x (cons2 z xs)) (recognise (step x z) xs))))
(assert (forall ((p R) (q R)) (= (formula p q nil) nil3)))
(assert
  (forall ((p R) (q R) (z list2) (s1 list) (s2 list))
    (= (formula p q (cons (pair2 s1 s2) z))
      (cons3 (and (recognise p s1) (recognise q s2)) (formula p q z)))))
(assert (= (split2 nil2) (cons (pair2 nil2 nil2) nil)))
(assert
  (not
    (forall ((p R) (q R) (s list))
      (= (recognise (Seq p q) s) (or2 (formula p q (split2 s)))))))
(check-sat)
