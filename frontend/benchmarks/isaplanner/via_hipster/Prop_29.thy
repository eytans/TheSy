theory Prop_29
imports Main
        "$HIPSTER_HOME/IsaHipster"
begin

datatype 'a ListSpecial = niltwoSpec | constwoSpec "'a" "'a ListSpecial"

datatype NatSpecial = Z | S "NatSpecial"

fun x :: "NatSpecial => NatSpecial => bool" where
"x (Z) (Z) = True"
| "x (Z) (S ztwoSpec) = False"
| "x (S xtwoSpec) (Z) = False"
| "x (S xtwoSpec) (S ytwoSpec) = x xtwoSpec ytwoSpec"

fun ins1 :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"ins1 y (niltwoSpec) = constwoSpec y (niltwoSpec)"
| "ins1 y (constwoSpec ztwoSpec xs) =
     (if x y ztwoSpec then constwoSpec ztwoSpec xs else constwoSpec ztwoSpec (ins1 y xs))"

fun elem :: "NatSpecial => NatSpecial ListSpecial => bool" where
"elem y (niltwoSpec) = False"
| "elem y (constwoSpec ztwoSpec xs) = (if x y ztwoSpec then True else elem y xs)"

hipster x ins1 elem
end
