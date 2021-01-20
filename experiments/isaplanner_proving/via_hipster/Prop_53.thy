theory Prop_53
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpec) = x xtwoSpec ytwoSpec"

fun count :: "NatSpecial => NatSpecial ListSpecial => NatSpecial" where
"count y (niltwoSpec) = Z"
| "count y (constwoSpec ztwoSpec ys) =
     (if x y ztwoSpec then S (count y ys) else count y ys)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) z = True"
| "twoSpec (S ztwoSpec) (Z) = False"
| "twoSpec (S ztwoSpec) (S xtwoSpec) = twoSpec ztwoSpec xtwoSpec"

fun insort :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"insort y (niltwoSpec) = constwoSpec y (niltwoSpec)"
| "insort y (constwoSpec ztwoSpec xs) =
     (if twoSpec y ztwoSpec then constwoSpec y (constwoSpec ztwoSpec xs) else constwoSpec ztwoSpec (insort y xs))"

fun sort :: "NatSpecial ListSpecial => NatSpecial ListSpecial" where
"sort (niltwoSpec) = niltwoSpec"
| "sort (constwoSpec z xs) = insort z (sort xs)"

hipster x count twoSpec insort sort
end
