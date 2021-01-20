theory Prop_63
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun len :: "'a ListSpecial => NatSpecial" where
"len (niltwoSpec) = Z"
| "len (constwoSpec y xs) = S (len xs)"

fun last :: "NatSpecial ListSpecial => NatSpecial" where
"last (niltwoSpec) = Z"
| "last (constwoSpec y (niltwoSpec)) = y"
| "last (constwoSpec y (constwoSpec xtwoSpec x3)) = last (constwoSpec xtwoSpec x3)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) y = y"
| "drop (S z) (niltwoSpec) = niltwoSpec"
| "drop (S z) (constwoSpec xtwoSpec x3) = drop z x3"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec x (Z) = False"
| "twoSpec (Z) (S z) = True"
| "twoSpec (S xtwoSpec) (S z) = twoSpec xtwoSpec z"

hipster len last drop twoSpec
end
