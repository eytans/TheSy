theory Prop_42
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun take :: "NatSpecial => 'a ListSpecial => 'a ListSpecial" where
"take (Z) y = niltwoSpec"
| "take (S z) (niltwoSpec) = niltwoSpec"
| "take (S z) (constwoSpec xtwoSpec x3) = constwoSpec xtwoSpec (take z x3)"

hipster take
end
