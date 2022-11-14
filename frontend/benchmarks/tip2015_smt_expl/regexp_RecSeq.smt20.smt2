(declare-sort sk2 0)
(declare-sort sk 0)
(declare-datatype
  pair4 ((pair23 (proj1-pair3 sk) (proj2-pair3 sk))))
(declare-datatype
  list5 ((nil5) (cons5 (head5 Bool) (tail5 list5))))
(declare-datatype list2 ((nil4) (cons4 (head4 sk) (tail4 list2))))
(declare-datatype
  pair3 ((pair22 (proj1-pair2 list2) (proj2-pair2 list2))))
(declare-datatype
  list4 ((nil2) (cons2 (head2 pair3) (tail2 list4))))
(declare-datatype A ((X) (Y)))
(declare-datatype
  R
  ((Nil) (Eps) (Atom (proj1-Atom A))
   (Plus (proj1-Plus R) (proj2-Plus R))
   (Seq (proj1-Seq R) (proj2-Seq R)) (Star (proj1-Star R))))
(declare-datatype list ((nil3) (cons3 (head3 A) (tail3 list))))
(declare-datatype
  pair ((pair2 (proj1-pair list) (proj2-pair list))))
(declare-datatype list3 ((nil) (cons (head pair) (tail list3))))
(declare-fun split (sk list4) list4)
(declare-fun split2 (list2) list4)
(declare-fun seq (R R) R)
(declare-fun plus (R R) R)
(declare-fun or2 (list5) Bool)
(declare-fun eqA (A A) Bool)
(declare-fun eps (R) Bool)
(declare-fun epsR (R) R)
(declare-fun step (R A) R)
(declare-fun recognise (R list) Bool)
(declare-fun formula (R R list3) list5)
(assert (not (or2 nil5)))
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
  (forall ((y Bool) (xs list5))
    (= (or2 (cons5 y xs)) (or y (or2 xs)))))
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
(assert (forall ((x R)) (= (recognise x nil3) (eps x))))
(assert
  (forall ((x R) (z A) (xs list))
    (= (recognise x (cons3 z xs)) (recognise (step x z) xs))))
(assert (forall ((p R) (q R)) (= (formula p q nil) nil5)))
(assert
  (forall ((p R) (q R) (z list3) (s1 list) (s2 list))
    (= (formula p q (cons (pair2 s1 s2) z))
      (cons5 (and (recognise p s1) (recognise q s2)) (formula p q z)))))
(assert (forall ((x sk)) (= (split x nil2) nil2)))
(assert
  (forall ((x sk) (x2 list4) (xs list2) (ys list2))
    (= (split x (cons2 (pair22 xs ys) x2))
      (cons2 (pair22 (cons4 x xs) ys) (split x x2)))))
(assert (= (split2 nil4) (cons2 (pair22 nil4 nil4) nil2)))
(assert
  (forall ((y sk) (s list2))
    (= (split2 (cons4 y s))
      (cons2 (pair22 nil4 (cons4 y s)) (split y (split2 s))))))
