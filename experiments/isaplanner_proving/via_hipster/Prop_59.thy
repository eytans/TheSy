theory Prop_59
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun last :: "NatSpecial ListSpecial => NatSpecial" where
"last (niltwoSpec) = Z"
| "last (constwoSpec z (niltwoSpec)) = z"
| "last (constwoSpec z (constwoSpec xtwoSpec x3)) = last (constwoSpec xtwoSpec x3)"

hipster x last
end
