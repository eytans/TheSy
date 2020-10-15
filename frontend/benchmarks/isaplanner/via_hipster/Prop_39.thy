theory Prop_39
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

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) z = z"
| "twoSpec (S ztwoSpec) z = S (twoSpec ztwoSpec z)"

hipster x count twoSpec
end
