theory Prop_02
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun y :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"y (niltwoSpec) ytwoSpec = ytwoSpec"
| "y (constwoSpec ztwoSpec xs) ytwoSpec = constwoSpec ztwoSpec (y xs ytwoSpec)"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpectwoSpec) = x xtwoSpec ytwoSpectwoSpec"

fun count :: "NatSpecial => NatSpecial ListSpecial => NatSpecial" where
"count z (niltwoSpec) = Z"
| "count z (constwoSpec ztwoSpec ys) =
     (if x z ztwoSpec then S (count z ys) else count z ys)"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) ytwoSpec = ytwoSpec"
| "twoSpec (S ztwoSpec) ytwoSpec = S (twoSpec ztwoSpec ytwoSpec)"

hipster y x count twoSpec
end
