theory Prop_23
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun max :: "NatSpecial => NatSpecial => NatSpecial" where
"max (Z) y = y"
| "max (S z) (Z) = S z"
| "max (S z) (S xtwoSpec) = S (max z xtwoSpec)"

hipster max
end
