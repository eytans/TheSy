theory Prop_24
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpec) = x xtwoSpec ytwoSpec"

fun max :: "NatSpecial => NatSpecial => NatSpecial" where
"max (Z) z = z"
| "max (S ztwoSpec) (Z) = S ztwoSpec"
| "max (S ztwoSpec) (S xtwoSpec) = S (max ztwoSpec xtwoSpec)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec (Z) z = True"
| "twoSpec (S ztwoSpec) (Z) = False"
| "twoSpec (S ztwoSpec) (S xtwoSpec) = twoSpec ztwoSpec xtwoSpec"

hipster x max twoSpec
end
