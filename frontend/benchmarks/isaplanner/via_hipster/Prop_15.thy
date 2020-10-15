theory Prop_15
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec y xs) = S (len xs)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec x (Z) = False"
| "twoSpec (Z) (S z) = True"
| "twoSpec (S xtwoSpec) (S z) = twoSpec xtwoSpec z"

fun ins :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"ins x (niltwoSpec) = constwoSpec x (niltwoSpec)"
| "ins x (constwoSpec z xs) =
     (if twoSpec x z then constwoSpec x (constwoSpec z xs) else constwoSpec z (ins x xs))"

hipster len twoSpec ins
end
