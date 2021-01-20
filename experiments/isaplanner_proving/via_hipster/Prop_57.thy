theory Prop_57
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) y = niltwoSpec"
| "take (S z) (niltwoSpec) = niltwoSpec"
| "take (S z) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take z x3)"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) y = y"
| "drop (S z) (niltwoSpec) = niltwoSpec"
| "drop (S z) (constwoSpec xtwoSpec x3) = drop z x3"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) y = Z"
| "twoSpec (S z) (Z) = S z"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster take drop twoSpec
end
