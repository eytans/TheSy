theory Prop_09
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun twoSpectwoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpectwoSpec (Z) y = y"
| "twoSpectwoSpec (S z) y = S (twoSpectwoSpec z y)"

fun twoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpec (Z) y = Z"
| "twoSpec (S z) (Z) = S z"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster twoSpectwoSpec twoSpec
end
