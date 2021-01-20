theory Prop_77
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "bool => bool => bool" where
"x True z = z"
| "x False z = False"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) z = True"
| "twoSpec (S ztwoSpec) (Z) = False"
| "twoSpec (S ztwoSpec) (S xtwoSpec) = twoSpec ztwoSpec xtwoSpec"

fun insort :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"insort y (niltwoSpec) = constwoSpec y (niltwoSpec)"
| "insort y (constwoSpec ztwoSpec xs) =
     (if twoSpec y ztwoSpec then constwoSpec y (constwoSpec ztwoSpec xs) else constwoSpec ztwoSpec (insort y xs))"

fun sorted :: "NatSpecial ListSpecial => bool" where
"sorted (niltwoSpec) = True"
| "sorted (constwoSpec z (niltwoSpec)) = True"
| "sorted (constwoSpec z (constwoSpec ytwoSpec ys)) =
     x (twoSpec z ytwoSpec) (sorted (constwoSpec ytwoSpec ys))"

hipster x twoSpec insort sorted
end
