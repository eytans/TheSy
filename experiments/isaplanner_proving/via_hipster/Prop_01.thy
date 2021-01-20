theory Prop_01
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "'a ListSpecial => 'a ListSpecial => 'a ListSpecial" where
"x (niltwoSpec) z = z"
| "x (constwoSpec ztwoSpec xs) z = constwoSpec ztwoSpec (x xs z)"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) z = niltwoSpec"
| "take (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "take (S ztwoSpec) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take ztwoSpec x3)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) z = z"
| "drop (S ztwoSpec) (niltwoSpec) = niltwoSpec"
| "drop (S ztwoSpec) (constwoSpec xtwoSpec x3) = drop ztwoSpec x3"

hipster x take drop
end
