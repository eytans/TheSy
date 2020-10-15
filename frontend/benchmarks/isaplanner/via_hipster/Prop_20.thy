theory Prop_20
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec y xs) = S (len xs)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) y = True"
| "twoSpec (S z) (Z) = False"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

fun insort :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"insort x (niltwoSpec) = constwoSpec x (niltwoSpec)"
| "insort x (constwoSpec z xs) =
     (if twoSpec x z then constwoSpec x (constwoSpec z xs) else constwoSpec z (insort x xs))"

fun sort :: "NatSpecial ListSpecial => NatSpecial ListSpecial" where
"sort (niltwoSpec) = niltwoSpec"
| "sort (constwoSpec y xs) = insort y (sort xs)"

hipster len twoSpec insort sort
end
