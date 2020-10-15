theory Prop_21
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun twoSpectwoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpectwoSpec (Z) y = y"
| "twoSpectwoSpec (S z) y = S (twoSpectwoSpec z y)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) y = True"
| "twoSpec (S z) (Z) = False"
| "twoSpec (S z) (S xtwoSpec) = twoSpec z xtwoSpec"

hipster twoSpectwoSpec twoSpec
end
