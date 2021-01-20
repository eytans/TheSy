theory Prop_67
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec y xs) = S (len xs)"

fun butlast :: "'a ListSpecial => 'a ListSpecial" where
"butlast (niltwoSpec) = niltwoSpec"
| "butlast (constwoSpec y (niltwoSpec)) = niltwoSpec"
| "butlast (constwoSpec y (constwoSpec xtwoSpec x3)) =
     constwoSpec y (butlast (constwoSpec xtwoSpec x3))"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) y = Z"
| "twoSpec (S z) (Z) = S z"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster len butlast twoSpec
end
