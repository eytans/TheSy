theory Prop_32
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun min :: "NatSpecial => NatSpecial => NatSpecial" where
"min (Z) y = Z"
| "min (S z) (Z) = Z"
| "min (S z) (S y1) = S (min z y1)"

hipster min
end
