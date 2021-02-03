theory TestDifficult
imports "$HIPSTER_HOME/IsaHipster"

begin

datatype 'a Lst =
  Emp
  | Cons "'a" "'a Lst"

datatype Nt = Z | S "Nt"

fun app :: "'a Lst ⇒ 'a Lst ⇒ 'a Lst"
where
  "app Emp xs = xs"
| "app (Cons x xs) ys = Cons x (app xs ys)"

fun take :: "Nt ⇒ 'a Lst ⇒ 'a Lst" where
  "take Z     _           = Emp"
| "take _     Emp         = Emp"
| "take (S n) (Cons t ts) = Cons t (take n ts)"

fun drop :: "Nt ⇒ 'a Lst ⇒ 'a Lst" where
  "drop Z     ts          = ts"
| "drop _     Emp         = Emp"
| "drop (S n) (Cons t ts) = drop n ts"

fun filter :: "('a ⇒ bool) ⇒ 'a Lst ⇒ 'a Lst" where
  "filter p Emp = Emp"
| "filter p (Cons x xs) = (if (p x) then (Cons x (filter p xs)) else (filter p xs))"

hipster app filter take drop