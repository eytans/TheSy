theory Prop_66
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec y xs) = S (len xs)"

fun filter :: "('a => bool) => 'a ListSpecial => 'a ListSpecial" where
"filter x (niltwoSpec) = niltwoSpec"
| "filter x (constwoSpec z xs) =
     (if x z then constwoSpec z (filter x xs) else filter x xs)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) y = True"
| "twoSpec (S z) (Z) = False"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster len filter twoSpec
end
