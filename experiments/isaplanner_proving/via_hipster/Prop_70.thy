theory Prop_70
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) y = True"
| "twoSpec (S z) (Z) = False"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster twoSpec
end
