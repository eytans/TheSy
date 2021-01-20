theory Prop_86
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

fun elem :: "NatSpecial => NatSpecial ListSpecial => bool" where
"elem y (niltwoSpec) = False"
| "elem y (constwoSpec ztwoSpec xs) = (if x y ztwoSpec then True else elem y xs)"

fun twoSpec :: "NatSpecial => NatSpecial => bool" where
"twoSpec y (Z) = False"
| "twoSpec (Z) (S ztwoSpec) = True"
| "twoSpec (S xtwoSpec) (S ztwoSpec) = twoSpec xtwoSpec ztwoSpec"

fun ins :: "NatSpecial => NatSpecial ListSpecial => NatSpecial ListSpecial" where
"ins y (niltwoSpec) = constwoSpec y (niltwoSpec)"
| "ins y (constwoSpec ztwoSpec xs) =
     (if twoSpec y ztwoSpec then constwoSpec y (constwoSpec ztwoSpec xs) else constwoSpec ztwoSpec (ins y xs))"

hipster x elem twoSpec ins
end
