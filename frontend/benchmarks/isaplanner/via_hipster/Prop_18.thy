theory Prop_18
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun twoSpectwoSpec :: "NatSpecial => NatSpecial => NatSpecial" where
"twoSpectwoSpec (Z) y = y"
| "twoSpectwoSpec (S z) y = S (twoSpectwoSpec z y)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec x (Z) = False"
| "twoSpec (Z) (S z) = True"
| "twoSpec (S xtwoSpec) (S z) = twoSpec xtwoSpec z"

hipster twoSpectwoSpec twoSpec
end
