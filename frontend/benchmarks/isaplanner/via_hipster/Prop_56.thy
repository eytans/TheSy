theory Prop_56
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) y = y"
| "drop (S z) (niltwoSpec) = niltwoSpec"
| "drop (S z) (constwoSpec xtwoSpec x3) = drop z x3"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) y = y"
| "twoSpec (S z) y = S (twoSpec z y)"

hipster drop twoSpec
end
