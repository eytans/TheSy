theory Prop_11
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun drop :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"drop (Z) y = y"
| "drop (S z) (niltwoSpec) = niltwoSpec"
| "drop (S z) (constwoSpec xtwoSpec x3) = drop z x3"

hipster drop
end
